-- Prove2me | solution 1 for TwoAgentSched.ParetoTotal.lemma_11_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:24:09.589693+00:00
-- url     : https://prove2.me/submissions/06aaf90b-7940-4088-9aa6-b7757c64eb41

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_TwoAgentSched_ParetoTotal_Model
import Theorems.Thm_TwoAgentSched_ParetoTotal_lemma_11_4

set_option autoImplicit false
open TwoAgentSched.ParetoTotal TwoAgentSched.TotalMax TwoAgentSched.MaxMax MooreLateJobs.Shared

section generic
variable {ι : Type*} [DecidableEq ι] (p : ι → ℝ)

lemma pt115_ca_append_left (l₁ l₂ : List ι) (m : ℕ) (hm : m < l₁.length) :
    completionAt p (l₁ ++ l₂) m = completionAt p l₁ m := by
  unfold completionAt
  rw [List.take_append_of_le_length (by omega)]

lemma pt115_ct_append_left (l₁ l₂ : List ι) (x : ι) (hx : x ∈ l₁) :
    completionTime p (l₁ ++ l₂) x = completionTime p l₁ x := by
  unfold completionTime
  rw [List.idxOf_append_of_mem hx]
  exact pt115_ca_append_left p l₁ l₂ _ (List.idxOf_lt_length_iff.mpr hx)

lemma pt115_ct_last (l : List ι) (z : ι) (hz : z ∉ l) :
    completionTime p (l ++ [z]) z = ((l ++ [z]).map p).sum := by
  unfold completionTime completionAt
  have h1 : (l ++ [z]).idxOf z = l.length := by
    rw [List.idxOf_append_of_notMem hz]; simp
  rw [h1]
  have h2 : (l ++ [z]).take (l.length + 1) = l ++ [z] := List.take_of_length_le (by simp)
  rw [h2]

lemma pt115_ct_append_right (l₁ l₂ : List ι) (x : ι) (hx : x ∉ l₁) :
    completionTime p (l₁ ++ l₂) x = (l₁.map p).sum + completionTime p l₂ x := by
  unfold completionTime completionAt
  rw [List.idxOf_append_of_notMem hx, List.take_append]
  have e1 : l₁.take (l₁.length + l₂.idxOf x + 1) = l₁ := List.take_of_length_le (by omega)
  have e3 : l₁.length + l₂.idxOf x + 1 - l₁.length = l₂.idxOf x + 1 := by omega
  rw [e1, e3]
  simp

lemma pt115_ct_erase_le (hp : ∀ j, 0 ≤ p j) (l : List ι) (hnd : l.Nodup) (z x : ι)
    (hz : z ∈ l) (hx : x ∈ l) (hxz : x ≠ z) :
    completionTime p (l.erase z) x ≤ completionTime p l x := by
  obtain ⟨a, b, rfl⟩ := List.append_of_mem hz
  have hza : z ∉ a := fun h => (List.nodup_append.1 hnd).2.2 z h z (by simp) rfl
  have herase : (a ++ z :: b).erase z = a ++ b := by
    rw [List.erase_append_right _ hza]; simp
  rw [herase]
  have hx' : x ∈ a ∨ x ∈ b := by
    rcases List.mem_append.1 hx with h | h
    · exact Or.inl h
    · rcases List.mem_cons.1 h with h | h
      · exact absurd h hxz
      · exact Or.inr h
  rcases hx' with hxa | hxb
  · rw [pt115_ct_append_left p a b x hxa, pt115_ct_append_left p a (z :: b) x hxa]
  · have hxa : x ∉ a := fun h => (List.nodup_append.1 hnd).2.2 x h x (by simp [hxb]) rfl
    unfold completionTime completionAt
    rw [List.idxOf_append_of_notMem hxa, List.idxOf_append_of_notMem hxa,
      List.idxOf_cons_ne _ (Ne.symm hxz)]
    rw [List.take_append, List.take_append]
    have e1 : a.take (a.length + List.idxOf x b + 1) = a := List.take_of_length_le (by omega)
    have e2 : a.take (a.length + (List.idxOf x b).succ + 1) = a :=
      List.take_of_length_le (by omega)
    rw [e1, e2]
    have e3 : a.length + List.idxOf x b + 1 - a.length = List.idxOf x b + 1 := by omega
    have e4 : a.length + (List.idxOf x b).succ + 1 - a.length = List.idxOf x b + 1 + 1 := by omega
    rw [e3, e4]
    simp only [List.take_succ_cons, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    linarith [hp z]

lemma pt115_sum_take_le (hp : ∀ j, 0 ≤ p j) (l : List ι) (m₁ m₂ : ℕ) (hle : m₁ ≤ m₂) :
    ((l.take m₁).map p).sum ≤ ((l.take m₂).map p).sum := by
  have h1 : l.take m₂ = l.take m₁ ++ (l.drop m₁).take (m₂ - m₁) := by
    rw [← List.take_add, Nat.add_sub_of_le hle]
  rw [h1, List.map_append, List.sum_append]
  have hnn : 0 ≤ (((l.drop m₁).take (m₂ - m₁)).map p).sum :=
    List.sum_nonneg (by intro x hx; rw [List.mem_map] at hx; obtain ⟨j, _, rfl⟩ := hx; exact hp j)
  linarith

lemma pt115_ct_mono_idxOf (hp : ∀ j, 0 ≤ p j) (l : List ι) (x y : ι)
    (hle : l.idxOf x ≤ l.idxOf y) :
    completionTime p l x ≤ completionTime p l y := by
  unfold completionTime completionAt
  exact pt115_sum_take_le p hp l (l.idxOf x + 1) (l.idxOf y + 1) (by omega)

end generic

instance {nA nB : ℕ} : LawfulBEq (Job nA nB) where
  eq_of_beq {a b} h := by
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (eq_of_beq h)
    · contradiction
    · contradiction
    · exact congrArg Sum.inr (eq_of_beq h)
  rfl {a} := by
    rcases a with a | a <;> exact beq_self_eq_true a

lemma pt115_beq_eq {nA nB : ℕ} (a z : Job nA nB) :
    @BEq.beq (Job nA nB) instBEqOfDecidableEq a z = (a == z) := by
  change decide (a = z) = (a == z)
  by_cases h : a = z
  · subst h; rw [decide_eq_true rfl, beq_self_eq_true]
  · rw [decide_eq_false h, beq_false_of_ne h]

lemma pt115_erase_eq {nA nB : ℕ} (l : List (Job nA nB)) (z : Job nA nB) :
    @List.erase (Job nA nB) instBEqOfDecidableEq l z = l.erase z := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.erase_cons, pt115_beq_eq, ih]

lemma pt115_idxOf_eq {nA nB : ℕ} (l : List (Job nA nB)) (z : Job nA nB) :
    @List.idxOf (Job nA nB) instBEqOfDecidableEq z l = l.idxOf z := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.idxOf_cons, pt115_beq_eq, ih]

lemma pt115_ct_erase_le' {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (l : List (Job nA nB)) (hnd : l.Nodup) (z x : Job nA nB)
    (hz : z ∈ l) (hx : x ∈ l) (hxz : x ≠ z) :
    completionTime p (l.erase z) x ≤ completionTime p l x := by
  rw [← pt115_erase_eq]
  exact pt115_ct_erase_le p hp l hnd z x hz hx hxz

lemma pt115_ct_mono_idxOf' {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (l : List (Job nA nB)) (x y : Job nA nB) (hle : l.idxOf x ≤ l.idxOf y) :
    completionTime p l x ≤ completionTime p l y := by
  apply pt115_ct_mono_idxOf p hp l x y
  rwa [pt115_idxOf_eq, pt115_idxOf_eq]

lemma opt_bPrecedesA_cost_gt {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (σ : List (Job nA nB)) (hσ : TwoAgentSched.TotalMax.IsOptimal p fB Q σ)
    (k : Fin nB) (j : Fin nA) (hkj : BPrecedesA σ k j) :
    Q < fB k (completionTime p σ (Sum.inl j)) := by
  have hp0 : ∀ x, 0 ≤ p x := fun x => (hp x).le
  by_contra hcon
  have hle_Q : fB k (completionTime p σ (Sum.inl j)) ≤ Q := not_lt.1 hcon
  have hjσ : (Sum.inl j : Job nA nB) ∈ σ := (hσ.1.1.2 _).2 (Finset.mem_univ _)
  have hkσ : (Sum.inr k : Job nA nB) ∈ σ := (hσ.1.1.2 _).2 (Finset.mem_univ _)
  set m := σ.idxOf (Sum.inl j) with hm_def
  have hm : m < σ.length := List.idxOf_lt_length_iff.2 hjσ
  have hgm : σ[m] = Sum.inl j := List.getElem_idxOf _
  set L := σ.take m with hL_def
  set l₁ := L ++ [Sum.inl j] with hl₁_def
  set l₂ := σ.drop (m + 1) with hl₂_def
  have hl₁_eq : σ.take (m + 1) = l₁ := by
    rw [List.take_add_one, List.getElem?_eq_getElem hm, Option.toList_some, ← hL_def, hgm]
  have hσ_split : σ = l₁ ++ l₂ := by
    rw [← hl₁_eq, hl₂_def, List.take_append_drop]
  have hnd : (l₁ ++ l₂).Nodup := hσ_split ▸ hσ.1.1.1
  have hnd₁ : l₁.Nodup := (List.nodup_append.1 hnd).1
  have hjL : (Sum.inl j : Job nA nB) ∉ L := fun h =>
    (List.nodup_append.1 hnd₁).2.2 _ h _ (by simp) rfl
  have hkL : (Sum.inr k : Job nA nB) ∈ L := by
    rw [hL_def, List.mem_take_iff_idxOf_lt hkσ]
    exact hkj
  have hkl₁ : (Sum.inr k : Job nA nB) ∈ l₁ := List.mem_append_left _ hkL
  set l₁' := l₁.erase (Sum.inr k) ++ [Sum.inr k] with hl₁'_def
  set σ' := l₁' ++ l₂ with hσ'_def
  have hperm₁ : l₁.Perm l₁' :=
    (List.perm_cons_erase hkl₁).trans (List.perm_append_singleton _ _).symm
  have hperm : σ.Perm σ' := by
    rw [hσ_split, hσ'_def]
    exact hperm₁.append_right l₂
  have hsched' : IsSchedule Finset.univ σ' :=
    ⟨hperm.nodup_iff.1 hσ.1.1.1, fun x => by rw [← hperm.mem_iff]; exact hσ.1.1.2 x⟩
  have hsum₁ : (l₁'.map p).sum = (l₁.map p).sum := (hperm₁.symm.map p).sum_eq
  have hct_j : completionTime p σ (Sum.inl j) = (l₁.map p).sum := by
    rw [hσ_split, pt115_ct_append_left p l₁ l₂ (Sum.inl j) (by simp [hl₁_def]),
      hl₁_def, pt115_ct_last p L (Sum.inl j) hjL]
  have hct_le_other : ∀ x : Job nA nB, x ≠ Sum.inr k →
      completionTime p σ' x ≤ completionTime p σ x := by
    intro x hxne
    by_cases hx₁ : x ∈ l₁
    · have hx_er : x ∈ l₁.erase (Sum.inr k) :=
        hnd₁.mem_erase_iff.2 ⟨hxne, hx₁⟩
      have hx₁' : x ∈ l₁' := List.mem_append_left _ hx_er
      rw [hσ'_def, pt115_ct_append_left p l₁' l₂ x hx₁',
        hl₁'_def, pt115_ct_append_left p (l₁.erase (Sum.inr k)) [Sum.inr k] x hx_er,
        hσ_split, pt115_ct_append_left p l₁ l₂ x hx₁]
      exact pt115_ct_erase_le' p hp0 l₁ hnd₁ (Sum.inr k) x hkl₁ hx₁ hxne
    · have hx₁' : x ∉ l₁' := fun h => hx₁ (hperm₁.symm.mem_iff.1 h)
      rw [hσ'_def, pt115_ct_append_right p l₁' l₂ x hx₁', hsum₁,
        hσ_split, pt115_ct_append_right p l₁ l₂ x hx₁]
  have hfeas' : IsFeasible p fB Q σ' := by
    refine ⟨hsched', fun k' => ?_⟩
    by_cases hk' : k' = k
    · subst hk'
      have hnot_er : (Sum.inr k' : Job nA nB) ∉ l₁.erase (Sum.inr k') :=
        List.Nodup.not_mem_erase hnd₁
      have hk₁' : (Sum.inr k' : Job nA nB) ∈ l₁' := by simp [hl₁'_def]
      rw [hσ'_def, pt115_ct_append_left p l₁' l₂ (Sum.inr k') hk₁',
        hl₁'_def, pt115_ct_last p _ (Sum.inr k') hnot_er,
        ← hl₁'_def, hsum₁, ← hct_j]
      exact hle_Q
    · have hne : (Sum.inr k' : Job nA nB) ≠ Sum.inr k := by simpa using hk'
      exact (hfB k' (hct_le_other (Sum.inr k') hne)).trans (hσ.1.2 k')
  have htot_lt : totalCompletionA p σ' < totalCompletionA p σ := by
    unfold totalCompletionA
    apply Finset.sum_lt_sum
    · intro h _
      exact hct_le_other (Sum.inl h) (by simp)
    · refine ⟨j, Finset.mem_univ _, ?_⟩
      have herase : l₁.erase (Sum.inr k) = L.erase (Sum.inr k) ++ [Sum.inl j] := by
        rw [hl₁_def, List.erase_append_left _ hkL]
      have hj_er : (Sum.inl j : Job nA nB) ∈ l₁.erase (Sum.inr k) := by
        rw [herase]; simp
      have hj₁' : (Sum.inl j : Job nA nB) ∈ l₁' := List.mem_append_left _ hj_er
      have hj_not_Ler : (Sum.inl j : Job nA nB) ∉ L.erase (Sum.inr k) := fun h =>
        hjL (List.mem_of_mem_erase h)
      rw [hσ'_def, pt115_ct_append_left p l₁' l₂ (Sum.inl j) hj₁',
        hl₁'_def, pt115_ct_append_left p (l₁.erase (Sum.inr k)) [Sum.inr k] (Sum.inl j) hj_er,
        herase, pt115_ct_last p (L.erase (Sum.inr k)) (Sum.inl j) hj_not_Ler, hct_j, hl₁_def]
      have hpermL := (List.perm_cons_erase hkL).map p
      have hsumL := hpermL.sum_eq
      simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_nil,
        List.sum_nil] at hsumL ⊢
      have := hp (Sum.inr k)
      linarith
  have hopt_le := hσ.2 σ' hfeas'
  linarith

theorem solution {nA nB : ℕ} (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q Q' : ℝ) (hQ : Q' < Q)
    (σ σ' : List (TwoAgentSched.MaxMax.Job nA nB)) (hσ : TwoAgentSched.TotalMax.IsOptimal p fB Q σ) (hσ' : TwoAgentSched.TotalMax.IsOptimal p fB Q' σ')
    (hspt : AFollowsSPT p σ) (hspt' : AFollowsSPT p σ') (k : Fin nB) (j : Fin nA)
    (hkj : BPrecedesA σ k j) :
    BPrecedesA σ' k j := by
  have hp0 : ∀ x, 0 ≤ p x := fun x => (hp x).le
  have hct_j_le : completionTime p σ (Sum.inl j) ≤ completionTime p σ' (Sum.inl j) :=
    lemma_11_4 p hp fB hfB Q Q' hQ σ σ' hσ hσ' hspt hspt' j
  have hQ_lt : Q < fB k (completionTime p σ (Sum.inl j)) :=
    opt_bPrecedesA_cost_gt p hp fB hfB Q σ hσ k j hkj
  have hfB_le : fB k (completionTime p σ' (Sum.inr k)) ≤ Q' := hσ'.1.2 k
  have hfB_j : fB k (completionTime p σ (Sum.inl j)) ≤ fB k (completionTime p σ' (Sum.inl j)) :=
    hfB k hct_j_le
  have hfB_lt : fB k (completionTime p σ' (Sum.inr k)) < fB k (completionTime p σ' (Sum.inl j)) := by
    linarith
  have hct_lt : completionTime p σ' (Sum.inr k) < completionTime p σ' (Sum.inl j) := by
    by_contra hcon
    exact not_le_of_gt hfB_lt (hfB k (not_lt.1 hcon))
  unfold BPrecedesA
  by_contra hcon
  have hidx_le : σ'.idxOf (Sum.inl j) ≤ σ'.idxOf (Sum.inr k) := not_lt.1 hcon
  have hct_ge := pt115_ct_mono_idxOf' p hp0 σ' (Sum.inl j) (Sum.inr k) hidx_le
  linarith

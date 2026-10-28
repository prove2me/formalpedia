-- Prove2me | solution 1 for TwoAgentSched.TotalMax.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:42:49.883036+00:00
-- url     : https://prove2.me/submissions/b66e91d4-d23e-4796-ae96-bfc8147a362b

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
import Definitions.Def_TwoAgentSched_TotalMax_BBlock

set_option autoImplicit false
open TwoAgentSched.TotalMax TwoAgentSched.MaxMax MooreLateJobs.Shared

section generic
variable {ι : Type*} [DecidableEq ι] (p : ι → ℝ)

lemma ttm56_ca_append_left (l₁ l₂ : List ι) (m : ℕ) (hm : m < l₁.length) :
    completionAt p (l₁ ++ l₂) m = completionAt p l₁ m := by
  unfold completionAt
  rw [List.take_append_of_le_length (by omega)]

lemma ttm56_ct_append_left (l₁ l₂ : List ι) (x : ι) (hx : x ∈ l₁) :
    completionTime p (l₁ ++ l₂) x = completionTime p l₁ x := by
  unfold completionTime
  rw [List.idxOf_append_of_mem hx]
  exact ttm56_ca_append_left p l₁ l₂ _ (List.idxOf_lt_length_iff.mpr hx)

lemma ttm56_ct_last (l : List ι) (z : ι) (hz : z ∉ l) :
    completionTime p (l ++ [z]) z = ((l ++ [z]).map p).sum := by
  unfold completionTime completionAt
  have h1 : (l ++ [z]).idxOf z = l.length := by
    rw [List.idxOf_append_of_notMem hz]; simp
  rw [h1]
  have h2 : (l ++ [z]).take (l.length + 1) = l ++ [z] := List.take_of_length_le (by simp)
  rw [h2]

lemma ttm56_ct_append_right (l₁ l₂ : List ι) (x : ι) (hx : x ∉ l₁) :
    completionTime p (l₁ ++ l₂) x = (l₁.map p).sum + completionTime p l₂ x := by
  unfold completionTime completionAt
  rw [List.idxOf_append_of_notMem hx]
  have h1 : l₁.length + List.idxOf x l₂ + 1 = l₁.length + (List.idxOf x l₂ + 1) := by omega
  rw [h1, List.take_append]
  have e1 : l₁.take (l₁.length + (l₂.idxOf x + 1)) = l₁ := List.take_of_length_le (by omega)
  have e3 : l₁.length + (l₂.idxOf x + 1) - l₁.length = l₂.idxOf x + 1 := by omega
  rw [e1, e3, List.map_append, List.sum_append]

lemma ttm56_ct_cons_ne (y : ι) (R : List ι) (x : ι) (hx : x ≠ y) :
    completionTime p (y :: R) x = p y + completionTime p R x := by
  unfold completionTime completionAt
  rw [List.idxOf_cons_ne _ (Ne.symm hx)]
  simp [List.take_succ_cons]

lemma ttm56_ct_cons_self (y : ι) (R : List ι) :
    completionTime p (y :: R) y = p y := by
  unfold completionTime completionAt
  simp

lemma ttm56_ct_erase_le (hp : ∀ j, 0 ≤ p j) (l : List ι) (hnd : l.Nodup) (z x : ι)
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
  · rw [ttm56_ct_append_left p a b x hxa, ttm56_ct_append_left p a (z :: b) x hxa]
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

lemma ttm56_start_eq_sum_take (l : List ι) (x : ι) (hx : x ∈ l) :
    completionTime p l x - p x = ((l.take (l.idxOf x)).map p).sum := by
  unfold completionTime completionAt
  have hm : l.idxOf x < l.length := List.idxOf_lt_length_iff.2 hx
  rw [List.take_add_one, List.getElem?_eq_getElem hm, Option.toList_some,
    List.getElem_idxOf, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
  ring

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

lemma ttm56_beq_eq {nA nB : ℕ} (a z : Job nA nB) :
    @BEq.beq (Job nA nB) instBEqOfDecidableEq a z = (a == z) := by
  change decide (a = z) = (a == z)
  by_cases h : a = z
  · subst h; rw [decide_eq_true rfl, beq_self_eq_true]
  · rw [decide_eq_false h, beq_false_of_ne h]

lemma ttm56_erase_eq {nA nB : ℕ} (l : List (Job nA nB)) (z : Job nA nB) :
    @List.erase (Job nA nB) instBEqOfDecidableEq l z = l.erase z := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.erase_cons, ttm56_beq_eq, ih]

lemma ttm56_idxOf_eq {nA nB : ℕ} (l : List (Job nA nB)) (z : Job nA nB) :
    @List.idxOf (Job nA nB) instBEqOfDecidableEq z l = l.idxOf z := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.idxOf_cons, ttm56_beq_eq, ih]

lemma ttm56_ct_erase_le' {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (l : List (Job nA nB)) (hnd : l.Nodup) (z x : Job nA nB)
    (hz : z ∈ l) (hx : x ∈ l) (hxz : x ≠ z) :
    completionTime p (l.erase z) x ≤ completionTime p l x := by
  rw [← ttm56_erase_eq]
  exact ttm56_ct_erase_le p hp l hnd z x hz hx hxz

lemma ttm56_start_eq_sum_take' {nA nB : ℕ} (p : Job nA nB → ℝ) (l : List (Job nA nB))
    (x : Job nA nB) (hx : x ∈ l) :
    completionTime p l x - p x = ((l.take (l.idxOf x)).map p).sum := by
  rw [← ttm56_idxOf_eq]
  exact ttm56_start_eq_sum_take p l x hx

lemma ttm56_ct_eq_sum_take' {nA nB : ℕ} (p : Job nA nB → ℝ) (l : List (Job nA nB))
    (x : Job nA nB) :
    completionTime p l x = ((l.take (l.idxOf x + 1)).map p).sum := by
  unfold completionTime completionAt
  rw [ttm56_idxOf_eq]

-- Step 1a: If B-job k precedes A-job j in an optimal schedule σ, then Q < fB k (C_j(σ))
lemma ttm56_opt_bPrecedesA_cost_gt {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (σ : List (Job nA nB)) (hσ : IsOptimal p fB Q σ)
    (k : Fin nB) (j : Fin nA) (hkj : σ.idxOf (Sum.inr k) < σ.idxOf (Sum.inl j)) :
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
    rw [hσ_split, ttm56_ct_append_left p l₁ l₂ (Sum.inl j) (by simp [hl₁_def]),
      hl₁_def, ttm56_ct_last p L (Sum.inl j) hjL]
  have hct_le_other : ∀ x : Job nA nB, x ≠ Sum.inr k →
      completionTime p σ' x ≤ completionTime p σ x := by
    intro x hxne
    by_cases hx₁ : x ∈ l₁
    · have hx_er : x ∈ l₁.erase (Sum.inr k) :=
        hnd₁.mem_erase_iff.2 ⟨hxne, hx₁⟩
      have hx₁' : x ∈ l₁' := List.mem_append_left _ hx_er
      rw [hσ'_def, ttm56_ct_append_left p l₁' l₂ x hx₁',
        hl₁'_def, ttm56_ct_append_left p (l₁.erase (Sum.inr k)) [Sum.inr k] x hx_er,
        hσ_split, ttm56_ct_append_left p l₁ l₂ x hx₁]
      exact ttm56_ct_erase_le' p hp0 l₁ hnd₁ (Sum.inr k) x hkl₁ hx₁ hxne
    · have hx₁' : x ∉ l₁' := fun h => hx₁ (hperm₁.symm.mem_iff.1 h)
      rw [hσ'_def, ttm56_ct_append_right p l₁' l₂ x hx₁', hsum₁,
        hσ_split, ttm56_ct_append_right p l₁ l₂ x hx₁]
  have hfeas' : IsFeasible p fB Q σ' := by
    refine ⟨hsched', fun k' => ?_⟩
    by_cases hk' : k' = k
    · subst hk'
      have hnot_er : (Sum.inr k' : Job nA nB) ∉ l₁.erase (Sum.inr k') :=
        List.Nodup.not_mem_erase hnd₁
      have hk₁' : (Sum.inr k' : Job nA nB) ∈ l₁' := by simp [hl₁'_def]
      rw [hσ'_def, ttm56_ct_append_left p l₁' l₂ (Sum.inr k') hk₁',
        hl₁'_def, ttm56_ct_last p _ (Sum.inr k') hnot_er,
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
      rw [hσ'_def, ttm56_ct_append_left p l₁' l₂ (Sum.inl j) hj₁',
        hl₁'_def, ttm56_ct_append_left p (l₁.erase (Sum.inr k)) [Sum.inr k] (Sum.inl j) hj_er,
        herase, ttm56_ct_last p (L.erase (Sum.inr k)) (Sum.inl j) hj_not_Ler, hct_j, hl₁_def]
      have hpermL := (List.perm_cons_erase hkL).map p
      have hsumL := hpermL.sum_eq
      simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_nil,
        List.sum_nil] at hsumL ⊢
      have := hp (Sum.inr k)
      linarith
  have hopt_le := hσ.2 σ' hfeas'
  linarith

-- Step 1b: In any optimal schedule σ, A-jobs appear in nondecreasing order of processing time
lemma ttm56_opt_a_mono_p {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (σ : List (Job nA nB)) (hσ : IsOptimal p fB Q σ)
    (h' h : Fin nA) (hh'h : σ.idxOf (Sum.inl h') < σ.idxOf (Sum.inl h)) :
    p (Sum.inl h') ≤ p (Sum.inl h) := by
  by_contra hcon
  have hlt : p (Sum.inl h) < p (Sum.inl h') := not_le.1 hcon
  have hhσ : (Sum.inl h : Job nA nB) ∈ σ := (hσ.1.1.2 _).2 (Finset.mem_univ _)
  have hh'σ : (Sum.inl h' : Job nA nB) ∈ σ := (hσ.1.1.2 _).2 (Finset.mem_univ _)
  set m := σ.idxOf (Sum.inl h) with hm_def
  have hm : m < σ.length := List.idxOf_lt_length_iff.2 hhσ
  have hgm : σ[m] = Sum.inl h := List.getElem_idxOf _
  set L := σ.take m with hL_def
  set l₃ := σ.drop (m + 1) with hl₃_def
  have hl₁_eq : σ.take (m + 1) = L ++ [Sum.inl h] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hm, Option.toList_some, ← hL_def, hgm]
  have hσ_split : σ = (L ++ [Sum.inl h]) ++ l₃ := by
    rw [← hl₁_eq, hl₃_def, List.take_append_drop]
  set a : Job nA nB := Sum.inl h' with ha
  set b : Job nA nB := Sum.inl h with hb
  have hab : a ≠ b := by
    intro e
    have : h' = h := by simpa [ha, hb] using e
    exact absurd hlt (by rw [ha, hb, this]; exact lt_irrefl _)
  have haL : a ∈ L := by
    rw [hL_def, List.mem_take_iff_idxOf_lt hh'σ]
    exact hh'h
  obtain ⟨L1, L2, hL_split⟩ := List.append_of_mem haL
  have hσ_eq : σ = ((L1 ++ a :: L2) ++ [b]) ++ l₃ := by
    rw [hσ_split, hL_split, hb]
  have hnd := hσ.1.1.1
  rw [hσ_eq] at hnd
  obtain ⟨hnd12, hnd3, hdisj3⟩ := List.nodup_append.1 hnd
  simp only [List.append_assoc, List.cons_append] at hnd12
  obtain ⟨hn1, hn2, hdisj⟩ := List.nodup_append.1 hnd12
  obtain ⟨ha_notin, hnd2⟩ := List.nodup_cons.1 hn2
  obtain ⟨hn3, hn4, hdisj2⟩ := List.nodup_append.1 hnd2
  have haL1 : a ∉ L1 := fun hx => hdisj a hx a (by simp) rfl
  have hbL1 : b ∉ L1 := fun hx => hdisj b hx b (by simp) rfl
  have haL2 : a ∉ L2 := fun hx => ha_notin (List.mem_append_left _ hx)
  have hbL2 : b ∉ L2 := fun hx => hdisj2 b hx b (by simp) rfl
  have hL12 : ∀ x ∈ L2, x ∉ L1 := fun x hx hx1 => hdisj x hx1 x (by simp [hx]) rfl
  set l₁ : List (Job nA nB) := (L1 ++ a :: L2) ++ [b] with hl₁
  set l₁' : List (Job nA nB) := L1 ++ (b :: (L2 ++ [a])) with hl₁'
  have hl₁_eq2 : l₁ = L1 ++ (a :: (L2 ++ [b])) := by simp [hl₁]
  have hperm₁ : l₁.Perm l₁' := by
    rw [hl₁_eq2, hl₁']
    refine List.Perm.append_left L1 ?_
    exact ((List.Perm.cons a (List.perm_append_singleton b L2)).trans
      (List.Perm.swap b a L2)).trans (List.Perm.cons b (List.perm_append_singleton a L2).symm)
  set σ' : List (Job nA nB) := l₁' ++ l₃ with hσ'
  have hperm : σ.Perm σ' := by
    rw [hσ_eq, hσ']
    exact hperm₁.append_right l₃
  have hs' : IsSchedule Finset.univ σ' :=
    ⟨hperm.nodup_iff.1 hσ.1.1.1, fun x => by rw [← hperm.mem_iff]; exact hσ.1.1.2 x⟩
  set S1 := (L1.map p).sum with hS1
  have hτ₁ : (l₁.map p).sum = (l₁'.map p).sum := (hperm₁.map p).sum_eq
  have c_left : ∀ x ∈ l₁, completionTime p σ x = completionTime p l₁ x := by
    intro x hx; rw [hσ_eq, ttm56_ct_append_left p l₁ l₃ x hx]
  have c_left' : ∀ x ∈ l₁', completionTime p σ' x = completionTime p l₁' x := by
    intro x hx; rw [hσ', ttm56_ct_append_left p l₁' l₃ x hx]
  have c1 : ∀ x ∈ L1, completionTime p σ' x = completionTime p σ x := by
    intro x hx
    have hx₁ : x ∈ l₁ := by simp [hl₁, hx]
    have hx₁' : x ∈ l₁' := by simp [hl₁', hx]
    rw [c_left' x hx₁', c_left x hx₁, hl₁_eq2, hl₁',
      ttm56_ct_append_left p _ _ x hx, ttm56_ct_append_left p _ _ x hx]
  have c2 : ∀ x ∈ L2, completionTime p σ' x = completionTime p σ x - (p a - p b) := by
    intro x hx
    have hxa : x ≠ a := fun e => haL2 (e ▸ hx)
    have hxb : x ≠ b := fun e => hbL2 (e ▸ hx)
    have hx₁ : x ∈ l₁ := by simp [hl₁, hx]
    have hx₁' : x ∈ l₁' := by simp [hl₁', hx]
    rw [c_left' x hx₁', c_left x hx₁, hl₁_eq2, hl₁',
      ttm56_ct_append_right p _ _ x (hL12 x hx), ttm56_ct_append_right p _ _ x (hL12 x hx),
      ttm56_ct_cons_ne p _ _ x hxa, ttm56_ct_cons_ne p _ _ x hxb,
      ttm56_ct_append_left p _ _ x hx, ttm56_ct_append_left p _ _ x hx]
    ring
  have c3 : ∀ x ∈ l₃, completionTime p σ' x = completionTime p σ x := by
    intro x hx
    have hnot₁ : x ∉ l₁ := fun hx₁ => hdisj3 x hx₁ x hx rfl
    have hnot₁' : x ∉ l₁' := fun hx₁' => hnot₁ (hperm₁.symm.mem_iff.1 hx₁')
    rw [hσ', ttm56_ct_append_right p l₁' l₃ x hnot₁', ← hτ₁,
      hσ_eq, ttm56_ct_append_right p l₁ l₃ x hnot₁]
  have c3a : completionTime p σ a = S1 + p a := by
    rw [c_left a (by simp [hl₁]), hl₁_eq2, ttm56_ct_append_right p _ _ a haL1, ttm56_ct_cons_self]
  have c3b : completionTime p σ' b = S1 + p b := by
    rw [c_left' b (by simp [hl₁']), hl₁', ttm56_ct_append_right p _ _ b hbL1, ttm56_ct_cons_self]
  have hbnot : b ∉ (L1 ++ a :: L2) := by
    intro hx
    rcases List.mem_append.1 hx with h1 | h1
    · exact hbL1 h1
    · rcases List.mem_cons.1 h1 with h2 | h2
      · exact hab h2.symm
      · exact hbL2 h2
  have hanot : a ∉ (L1 ++ b :: L2) := by
    intro hx
    rcases List.mem_append.1 hx with h1 | h1
    · exact haL1 h1
    · rcases List.mem_cons.1 h1 with h2 | h2
      · exact hab h2
      · exact haL2 h2
  have c4b : completionTime p σ b = (l₁.map p).sum := by
    rw [c_left b (by simp [hl₁]), hl₁]; exact ttm56_ct_last p _ b hbnot
  have c4a : completionTime p σ' a = (l₁'.map p).sum := by
    have : l₁' = (L1 ++ b :: L2) ++ [a] := by simp [hl₁']
    rw [c_left' a (by simp [hl₁']), this]; exact ttm56_ct_last p _ a hanot
  have hcls : ∀ x : Job nA nB, x ≠ a → x ≠ b → x ∈ L1 ∨ x ∈ L2 ∨ x ∈ l₃ := by
    intro x hxa hxb
    have : x ∈ σ := (hσ.1.1.2 x).2 (Finset.mem_univ _)
    rw [hσ_eq, hl₁] at this
    simp only [List.mem_append, List.mem_cons, List.mem_singleton] at this
    tauto
  have hfeas' : IsFeasible p fB Q σ' := by
    refine ⟨hs', fun k => ?_⟩
    have hxa : (Sum.inr k : Job nA nB) ≠ a := by simp [ha]
    have hxb : (Sum.inr k : Job nA nB) ≠ b := by simp [hb]
    have hB' := hσ.1.2 k
    rcases hcls _ hxa hxb with h1 | h1 | h1
    · rw [c1 _ h1]; exact hB'
    · rw [c2 _ h1]
      refine le_trans (hfB k ?_) hB'
      linarith
    · rw [c3 _ h1]; exact hB'
  have htot_lt : totalCompletionA p σ' < totalCompletionA p σ := by
    unfold totalCompletionA
    have hG1 : ∀ h'' : Fin nA, h'' ≠ h → h'' ≠ h' →
        completionTime p σ' (Sum.inl h'') - completionTime p σ (Sum.inl h'') ≤ 0 := by
      intro h'' h1 h2
      have hxa : (Sum.inl h'' : Job nA nB) ≠ a := by simp [ha, h2]
      have hxb : (Sum.inl h'' : Job nA nB) ≠ b := by simp [hb, h1]
      rcases hcls _ hxa hxb with h3 | h3 | h3
      · rw [c1 _ h3]; simp
      · rw [c2 _ h3]; linarith
      · rw [c3 _ h3]; simp
    have hpair : ∑ x ∈ ({h, h'} : Finset (Fin nA)),
        -(completionTime p σ' (Sum.inl x) - completionTime p σ (Sum.inl x)) = p a - p b := by
      have hne : h ≠ h' := fun e => hab (by rw [ha, hb, e])
      rw [Finset.sum_pair hne]
      have e1 : completionTime p σ' (Sum.inl h') = (l₁'.map p).sum := c4a
      have e2 : completionTime p σ (Sum.inl h) = (l₁.map p).sum := c4b
      have e3 : completionTime p σ (Sum.inl h') = S1 + p a := c3a
      have e4 : completionTime p σ' (Sum.inl h) = S1 + p b := c3b
      rw [e1, e2, e3, e4, ← hτ₁]
      ring
    have hsub : ({h, h'} : Finset (Fin nA)) ⊆ Finset.univ := Finset.subset_univ _
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun x => -(completionTime p σ' (Sum.inl x) - completionTime p σ (Sum.inl x))) hsub
      (by
        intro x _ hx
        have h1 : x ≠ h := fun e => hx (by simp [e])
        have h2 : x ≠ h' := fun e => hx (by simp [e])
        have := hG1 x h1 h2
        linarith)
    rw [hpair] at hle
    rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib] at hle
    have hpos : 0 < p a - p b := by rw [ha, hb]; linarith
    linarith
  have := hσ.2 σ' hfeas'
  linarith

-- Step 2: Prefix A/B decomposition and downward-closed A-job sum comparison
def aPrefSet {nA nB : ℕ} (l : List (Job nA nB)) (m : ℕ) : Finset (Fin nA) :=
  Finset.univ.filter (fun h => l.idxOf (Sum.inl h) < m)

def bPrefSet {nA nB : ℕ} (l : List (Job nA nB)) (m : ℕ) : Finset (Fin nB) :=
  Finset.univ.filter (fun k => l.idxOf (Sum.inr k) < m)

def aCount {nA nB : ℕ} (l : List (Job nA nB)) (k : Fin nB) : ℕ :=
  (aPrefSet l (l.idxOf (Sum.inr k))).card

lemma sum_take_eq_aPref_add_bPref {nA nB : ℕ} (p : Job nA nB → ℝ)
    (l : List (Job nA nB)) (hl : IsSchedule Finset.univ l) (m : ℕ) :
    ((l.take m).map p).sum =
      ∑ h ∈ aPrefSet l m, p (Sum.inl h) + ∑ k ∈ bPrefSet l m, p (Sum.inr k) := by
  rw [← List.sum_toFinset p hl.1.take]
  have hto : (l.take m).toFinset = Finset.univ.filter (fun x : Job nA nB => l.idxOf x < m) := by
    ext x
    rw [List.mem_toFinset, Finset.mem_filter]
    have hx : x ∈ l := (hl.2 x).2 (Finset.mem_univ x)
    rw [List.mem_take_iff_idxOf_lt hx]
    simp [Finset.mem_univ]
  rw [hto, Finset.sum_filter, Fintype.sum_sum_type, ← Finset.sum_filter, ← Finset.sum_filter]
  rfl

lemma sum_a_le_of_card_le {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (A₁ A₂ : Finset (Fin nA))
    (hd₁ : ∀ h ∈ A₁, ∀ h' ∉ A₁, p (Sum.inl h) ≤ p (Sum.inl h'))
    (hd₂ : ∀ h ∈ A₂, ∀ h' ∉ A₂, p (Sum.inl h) ≤ p (Sum.inl h'))
    (hcard : A₁.card ≤ A₂.card) :
    ∑ h ∈ A₁, p (Sum.inl h) ≤ ∑ h ∈ A₂, p (Sum.inl h) := by
  by_cases hsub : A₁ ⊆ A₂
  · exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun h _ _ => hp (Sum.inl h))
  · obtain ⟨h0, hh0₁, hh0₂⟩ := Finset.not_subset.1 hsub
    have hh0_sdiff : h0 ∈ A₁ \ A₂ := Finset.mem_sdiff.2 ⟨hh0₁, hh0₂⟩
    have hc_eq₁ : (A₁ ∩ A₂).card + (A₁ \ A₂).card = A₁.card := Finset.card_inter_add_card_sdiff A₁ A₂
    have hc_eq₂ : (A₂ ∩ A₁).card + (A₂ \ A₁).card = A₂.card := Finset.card_inter_add_card_sdiff A₂ A₁
    rw [Finset.inter_comm A₂ A₁] at hc_eq₂
    have hcard_sdiff : (A₁ \ A₂).card ≤ (A₂ \ A₁).card := by omega
    have hpos₁ : 0 < (A₁ \ A₂).card := Finset.card_pos.2 ⟨h0, hh0_sdiff⟩
    have hpos₂ : 0 < (A₂ \ A₁).card := lt_of_lt_of_le hpos₁ hcard_sdiff
    obtain ⟨h0', hh0'_sdiff⟩ := Finset.card_pos.1 hpos₂
    have hconst : ∀ h₁ ∈ A₁ \ A₂, ∀ h₂ ∈ A₂ \ A₁, p (Sum.inl h₁) = p (Sum.inl h₂) := by
      intro h₁ hh₁ h₂ hh₂
      rw [Finset.mem_sdiff] at hh₁ hh₂
      exact le_antisymm (hd₁ h₁ hh₁.1 h₂ hh₂.2) (hd₂ h₂ hh₂.1 h₁ hh₁.2)
    have hsum_sdiff₁ : ∑ h ∈ A₁ \ A₂, p (Sum.inl h) = (A₁ \ A₂).card * p (Sum.inl h0') := by
      have : ∑ h ∈ A₁ \ A₂, p (Sum.inl h) = ∑ _ ∈ A₁ \ A₂, p (Sum.inl h0') :=
        Finset.sum_congr rfl (fun h₁ hh₁ => hconst h₁ hh₁ h0' hh0'_sdiff)
      rw [this, Finset.sum_const, nsmul_eq_mul]
    have hsum_sdiff₂ : ∑ h ∈ A₂ \ A₁, p (Sum.inl h) = (A₂ \ A₁).card * p (Sum.inl h0') := by
      have : ∑ h ∈ A₂ \ A₁, p (Sum.inl h) = ∑ _ ∈ A₂ \ A₁, p (Sum.inl h0') :=
        Finset.sum_congr rfl (fun h₂ hh₂ =>
          (hconst h0 hh0_sdiff h₂ hh₂).symm.trans (hconst h0 hh0_sdiff h0' hh0'_sdiff))
      rw [this, Finset.sum_const, nsmul_eq_mul]
    have hs₁ : ∑ h ∈ A₁, p (Sum.inl h) =
        ∑ h ∈ A₁ ∩ A₂, p (Sum.inl h) + ∑ h ∈ A₁ \ A₂, p (Sum.inl h) := by
      have hdisj : Disjoint (A₁ ∩ A₂) (A₁ \ A₂) :=
        Finset.disjoint_left.2 (fun x hx1 hx2 => (Finset.mem_sdiff.1 hx2).2 (Finset.mem_inter.1 hx1).2)
      have hun : (A₁ ∩ A₂) ∪ (A₁ \ A₂) = A₁ := by ext x; simp; tauto
      rw [← Finset.sum_union hdisj, hun]
    have hs₂ : ∑ h ∈ A₂, p (Sum.inl h) =
        ∑ h ∈ A₁ ∩ A₂, p (Sum.inl h) + ∑ h ∈ A₂ \ A₁, p (Sum.inl h) := by
      have hdisj : Disjoint (A₂ ∩ A₁) (A₂ \ A₁) :=
        Finset.disjoint_left.2 (fun x hx1 hx2 => (Finset.mem_sdiff.1 hx2).2 (Finset.mem_inter.1 hx1).2)
      have hun : (A₂ ∩ A₁) ∪ (A₂ \ A₁) = A₂ := by ext x; simp; tauto
      have : A₂ ∩ A₁ = A₁ ∩ A₂ := Finset.inter_comm A₂ A₁
      rw [← this, ← Finset.sum_union hdisj, hun]
    have hle_mul : ((A₁ \ A₂).card : ℝ) * p (Sum.inl h0') ≤ ((A₂ \ A₁).card : ℝ) * p (Sum.inl h0') :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.2 hcard_sdiff) (hp (Sum.inl h0'))
    linarith

lemma opt_aPref_downward {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (σ : List (Job nA nB)) (hσ : IsOptimal p fB Q σ) (m : ℕ) :
    ∀ h ∈ aPrefSet σ m, ∀ h' ∉ aPrefSet σ m, p (Sum.inl h) ≤ p (Sum.inl h') := by
  intro h hh h' hh'
  rw [aPrefSet, Finset.mem_filter] at hh hh'
  have hge : m ≤ σ.idxOf (Sum.inl h') := not_lt.1 (fun hlt => hh' ⟨Finset.mem_univ _, hlt⟩)
  exact ttm56_opt_a_mono_p p hp fB hfB Q σ hσ h h' (lt_of_lt_of_le hh.2 hge)

lemma opt_sum_take_le {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (σ₁ σ₂ : List (Job nA nB)) (hσ₁ : IsOptimal p fB Q σ₁) (hσ₂ : IsOptimal p fB Q σ₂)
    (m₁ m₂ : ℕ)
    (ha : (aPrefSet σ₁ m₁).card ≤ (aPrefSet σ₂ m₂).card)
    (hb : bPrefSet σ₁ m₁ ⊆ bPrefSet σ₂ m₂) :
    ((σ₁.take m₁).map p).sum ≤ ((σ₂.take m₂).map p).sum := by
  have hp0 : ∀ j, 0 ≤ p j := fun j => (hp j).le
  rw [sum_take_eq_aPref_add_bPref p σ₁ hσ₁.1.1 m₁, sum_take_eq_aPref_add_bPref p σ₂ hσ₂.1.1 m₂]
  have hle_a := sum_a_le_of_card_le p hp0 (aPrefSet σ₁ m₁) (aPrefSet σ₂ m₂)
    (opt_aPref_downward p hp fB hfB Q σ₁ hσ₁ m₁)
    (opt_aPref_downward p hp fB hfB Q σ₂ hσ₂ m₂) ha
  have hle_b := Finset.sum_le_sum_of_subset_of_nonneg hb (fun k _ _ => hp0 (Sum.inr k))
  linarith

-- Step 3: Basic properties of aPrefSet and aCount
lemma aPrefSet_mono {nA nB : ℕ} (l : List (Job nA nB)) {m₁ m₂ : ℕ} (hle : m₁ ≤ m₂) :
    aPrefSet l m₁ ⊆ aPrefSet l m₂ := by
  intro h hh
  rw [aPrefSet, Finset.mem_filter] at hh ⊢
  exact ⟨hh.1, lt_of_lt_of_le hh.2 hle⟩

lemma aCount_mono {nA nB : ℕ} (l : List (Job nA nB)) {k₁ k₂ : Fin nB}
    (hle : l.idxOf (Sum.inr k₁) ≤ l.idxOf (Sum.inr k₂)) :
    aCount l k₁ ≤ aCount l k₂ :=
  Finset.card_le_card (aPrefSet_mono l hle)

lemma aPrefSet_inr_succ {nA nB : ℕ} (l : List (Job nA nB)) (hl : IsSchedule Finset.univ l)
    (k : Fin nB) :
    aPrefSet l (l.idxOf (Sum.inr k) + 1) = aPrefSet l (l.idxOf (Sum.inr k)) := by
  ext h
  rw [aPrefSet, aPrefSet, Finset.mem_filter, Finset.mem_filter]
  have hh : (Sum.inl h : Job nA nB) ∈ l := (hl.2 _).2 (Finset.mem_univ _)
  have hne : l.idxOf (Sum.inl h) ≠ l.idxOf (Sum.inr k) :=
    fun heq => by have := (List.idxOf_inj hh).1 heq; simp at this
  constructor
  · rintro ⟨hu, hlt⟩; exact ⟨hu, by omega⟩
  · rintro ⟨hu, hlt⟩; exact ⟨hu, by omega⟩

-- Step 4: For any two optimal schedules σ₁, σ₂, aCount σ₁ k = aCount σ₂ k for all k
lemma opt_aCount_le {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (σ₁ σ₂ : List (Job nA nB)) (hσ₁ : IsOptimal p fB Q σ₁) (hσ₂ : IsOptimal p fB Q σ₂)
    (k0 : Fin nB) :
    aCount σ₂ k0 ≤ aCount σ₁ k0 := by
  by_contra hcon
  have hlt0 : aCount σ₁ k0 < aCount σ₂ k0 := not_le.1 hcon
  -- Since aCount σ₁ k0 < aCount σ₂ k0 ≤ nA, there is some A-job after k0 in σ₁
  have hlt_nA : (aPrefSet σ₁ (σ₁.idxOf (Sum.inr k0))).card < (Finset.univ : Finset (Fin nA)).card := by
    have hle2 : aCount σ₂ k0 ≤ (Finset.univ : Finset (Fin nA)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    unfold aCount at hlt0 hle2
    omega
  have hnot_univ : aPrefSet σ₁ (σ₁.idxOf (Sum.inr k0)) ≠ Finset.univ := by
    intro heq; rw [heq] at hlt_nA; exact lt_irrefl _ hlt_nA
  obtain ⟨h_ex, _, hh_ex_not⟩ := Finset.not_subset.1 (fun hsub =>
    hnot_univ (Finset.Subset.antisymm (Finset.subset_univ _) hsub))
  set A_after : Finset (Fin nA) :=
    Finset.univ.filter (fun h => σ₁.idxOf (Sum.inr k0) < σ₁.idxOf (Sum.inl h))
  have hh_ex_after : h_ex ∈ A_after := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [aPrefSet, Finset.mem_filter] at hh_ex_not
    have hge : σ₁.idxOf (Sum.inr k0) ≤ σ₁.idxOf (Sum.inl h_ex) :=
      not_lt.1 (fun hlt => hh_ex_not ⟨Finset.mem_univ _, hlt⟩)
    have hh_in : (Sum.inl h_ex : Job nA nB) ∈ σ₁ := (hσ₁.1.1.2 _).2 (Finset.mem_univ _)
    have hne : σ₁.idxOf (Sum.inr k0) ≠ σ₁.idxOf (Sum.inl h_ex) :=
      fun heq => by have := (List.idxOf_inj hh_in).1 heq.symm; simp at this
    exact lt_of_le_of_ne hge hne
  obtain ⟨j, hj_after, hj_min⟩ :=
    Finset.exists_min_image A_after (fun h => σ₁.idxOf (Sum.inl h)) ⟨h_ex, hh_ex_after⟩
  have hk0_lt_j : σ₁.idxOf (Sum.inr k0) < σ₁.idxOf (Sum.inl j) :=
    (Finset.mem_filter.1 hj_after).2
  -- Show aPrefSet σ₁ (σ₁.idxOf (Sum.inl j) + 1) = insert j (aPrefSet σ₁ (σ₁.idxOf (Sum.inr k0)))
  have ha_eq : aPrefSet σ₁ (σ₁.idxOf (Sum.inl j) + 1) =
      insert j (aPrefSet σ₁ (σ₁.idxOf (Sum.inr k0))) := by
    ext h
    rw [aPrefSet, Finset.mem_insert, aPrefSet, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨_, hlt⟩
      by_cases hhj : h = j
      · exact Or.inl hhj
      · right
        refine ⟨Finset.mem_univ _, ?_⟩
        by_contra hnot_lt
        have hge : σ₁.idxOf (Sum.inr k0) ≤ σ₁.idxOf (Sum.inl h) := not_lt.1 hnot_lt
        have hh_in : (Sum.inl h : Job nA nB) ∈ σ₁ := (hσ₁.1.1.2 _).2 (Finset.mem_univ _)
        have hj_in : (Sum.inl j : Job nA nB) ∈ σ₁ := (hσ₁.1.1.2 _).2 (Finset.mem_univ _)
        have hne_k0 : σ₁.idxOf (Sum.inr k0) ≠ σ₁.idxOf (Sum.inl h) :=
          fun heq => by have := (List.idxOf_inj hh_in).1 heq.symm; simp at this
        have hh_mem_after : h ∈ A_after :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_le_of_ne hge hne_k0⟩
        have hj_le_h := hj_min h hh_mem_after
        have hne_idx : σ₁.idxOf (Sum.inl h) ≠ σ₁.idxOf (Sum.inl j) :=
          fun heq => hhj (Sum.inl_injective ((List.idxOf_inj hh_in).1 heq))
        omega
    · rintro (rfl | ⟨_, hlt⟩)
      · exact ⟨Finset.mem_univ _, by omega⟩
      · exact ⟨Finset.mem_univ _, by omega⟩
  have hj_not_in : j ∉ aPrefSet σ₁ (σ₁.idxOf (Sum.inr k0)) := by
    rw [aPrefSet, Finset.mem_filter]
    rintro ⟨_, hlt⟩; omega
  have ha_card : (aPrefSet σ₁ (σ₁.idxOf (Sum.inl j) + 1)).card = aCount σ₁ k0 + 1 := by
    rw [ha_eq, Finset.card_insert_of_notMem hj_not_in]; rfl
  -- Now choose kstar maximizing σ₂.idxOf among B-jobs before j in σ₁ with aCount σ₂ k ≥ aCount σ₁ k0 + 1
  set S : Finset (Fin nB) := Finset.univ.filter (fun k =>
    σ₁.idxOf (Sum.inr k) < σ₁.idxOf (Sum.inl j) ∧
    aCount σ₁ k0 + 1 ≤ aCount σ₂ k)
  have hk0_S : k0 ∈ S := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hk0_lt_j, by omega⟩
  obtain ⟨kstar, hkstar_S, hkstar_max⟩ :=
    Finset.exists_max_image S (fun k => σ₂.idxOf (Sum.inr k)) ⟨k0, hk0_S⟩
  obtain ⟨_, hkstar_lt_j, hkstar_ac⟩ := Finset.mem_filter.1 hkstar_S
  -- Compare prefix of σ₁ up to j+1 with prefix of σ₂ up to kstar+1
  have hct_le : completionTime p σ₁ (Sum.inl j) ≤ completionTime p σ₂ (Sum.inr kstar) := by
    rw [ttm56_ct_eq_sum_take', ttm56_ct_eq_sum_take']
    apply opt_sum_take_le p hp fB hfB Q σ₁ σ₂ hσ₁ hσ₂
    · rw [ha_card, aPrefSet_inr_succ σ₂ hσ₂.1.1 kstar]
      exact hkstar_ac
    · intro k hk
      rw [bPrefSet, Finset.mem_filter] at hk ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have hk_in₁ : (Sum.inr k : Job nA nB) ∈ σ₁ := (hσ₁.1.1.2 _).2 (Finset.mem_univ _)
      have hne_kj : σ₁.idxOf (Sum.inr k) ≠ σ₁.idxOf (Sum.inl j) :=
        fun heq => by have := (List.idxOf_inj hk_in₁).1 heq; simp at this
      have hk_lt_j : σ₁.idxOf (Sum.inr k) < σ₁.idxOf (Sum.inl j) := by omega
      by_cases hac : aCount σ₁ k0 + 1 ≤ aCount σ₂ k
      · have hk_S : k ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk_lt_j, hac⟩
        have := hkstar_max k hk_S
        omega
      · have hac_lt : aCount σ₂ k < aCount σ₂ kstar := by omega
        by_contra hnot_lt2
        have hge2 : σ₂.idxOf (Sum.inr kstar) ≤ σ₂.idxOf (Sum.inr k) := by omega
        have := aCount_mono σ₂ hge2
        omega
  have hQ_lt := ttm56_opt_bPrecedesA_cost_gt p hp fB hfB Q σ₁ hσ₁ kstar j hkstar_lt_j
  have hfB_le := hfB kstar hct_le
  have hfB_Q := hσ₂.1.2 kstar
  linarith

lemma opt_aCount_eq {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (σ₁ σ₂ : List (Job nA nB)) (hσ₁ : IsOptimal p fB Q σ₁) (hσ₂ : IsOptimal p fB Q σ₂)
    (k : Fin nB) :
    aCount σ₁ k = aCount σ₂ k :=
  le_antisymm (opt_aCount_le p hp fB hfB Q σ₂ σ₁ hσ₂ hσ₁ k)
    (opt_aCount_le p hp fB hfB Q σ₁ σ₂ hσ₁ hσ₂ k)

-- Step 5: SameBBlock l k k' ↔ aCount l k = aCount l k'
lemma sameBBlock_iff_aCount_eq {nA nB : ℕ} (l : List (Job nA nB))
    (hl : IsSchedule Finset.univ l) (k k' : Fin nB) :
    SameBBlock l k k' ↔ aCount l k = aCount l k' := by
  unfold SameBBlock aCount
  have h_le : ∀ k₁ k₂ : Fin nB,
      l.idxOf (Sum.inr k₁) ≤ l.idxOf (Sum.inr k₂) →
      ((∀ h : Fin nA, ¬ (l.idxOf (Sum.inr k₁) < l.idxOf (Sum.inl h) ∧
          l.idxOf (Sum.inl h) < l.idxOf (Sum.inr k₂))) ↔
        (aPrefSet l (l.idxOf (Sum.inr k₁))).card = (aPrefSet l (l.idxOf (Sum.inr k₂))).card) := by
    intro k₁ k₂ hle
    have hsub : aPrefSet l (l.idxOf (Sum.inr k₁)) ⊆ aPrefSet l (l.idxOf (Sum.inr k₂)) :=
      aPrefSet_mono l hle
    constructor
    · intro hno
      apply congrArg Finset.card
      apply Finset.Subset.antisymm hsub
      intro h hh₂
      rw [aPrefSet, Finset.mem_filter] at hh₂ ⊢
      refine ⟨hh₂.1, ?_⟩
      by_contra hnot
      have hh_in : (Sum.inl h : Job nA nB) ∈ l := (hl.2 _).2 (Finset.mem_univ _)
      have hne : l.idxOf (Sum.inr k₁) ≠ l.idxOf (Sum.inl h) :=
        fun heq => by have := (List.idxOf_inj hh_in).1 heq.symm; simp at this
      exact hno h ⟨lt_of_le_of_ne (not_lt.1 hnot) hne, hh₂.2⟩
    · intro hcard h ⟨hlt1, hlt2⟩
      have heq : aPrefSet l (l.idxOf (Sum.inr k₁)) = aPrefSet l (l.idxOf (Sum.inr k₂)) :=
        Finset.eq_of_subset_of_card_le hsub (by omega)
      have hh₂ : h ∈ aPrefSet l (l.idxOf (Sum.inr k₂)) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt2⟩
      rw [← heq, aPrefSet, Finset.mem_filter] at hh₂
      omega
  rcases le_total (l.idxOf (Sum.inr k)) (l.idxOf (Sum.inr k')) with hle | hle
  · simp only [min_eq_left hle, max_eq_right hle]
    exact h_le k k' hle
  · simp only [min_eq_right hle, max_eq_left hle]
    rw [h_le k' k hle, eq_comm]

-- Step 6: Express blockStart and blockEnd via aCount
open Classical in
lemma blockStart_eq_min_bBlock {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (l : List (Job nA nB)) (hl : IsSchedule Finset.univ l) (k : Fin nB) :
    ∃ kmin ∈ bBlock l k,
      (∀ k' ∈ bBlock l k, l.idxOf (Sum.inr kmin) ≤ l.idxOf (Sum.inr k')) ∧
      blockStart p l k = ((l.take (l.idxOf (Sum.inr kmin))).map p).sum ∧
      aCount l kmin = aCount l k ∧
      bPrefSet l (l.idxOf (Sum.inr kmin)) =
        Finset.univ.filter (fun k'' => aCount l k'' < aCount l k) := by
  obtain ⟨kmin, hkmin_mem, hkmin_min⟩ :=
    Finset.exists_min_image (bBlock l k) (fun k' => l.idxOf (Sum.inr k')) ⟨k, mem_bBlock_self l k⟩
  have hac_eq : aCount l kmin = aCount l k := by
    have hkmin_same : SameBBlock l k kmin := (Finset.mem_filter.1 hkmin_mem).2
    exact ((sameBBlock_iff_aCount_eq l hl k kmin).1 hkmin_same).symm
  refine ⟨kmin, hkmin_mem, hkmin_min, ?_, hac_eq, ?_⟩
  · unfold blockStart
    apply le_antisymm
    · have hle := Finset.inf'_le
        (f := fun k' => completionTime p l (Sum.inr k') - p (Sum.inr k')) hkmin_mem
      rwa [ttm56_start_eq_sum_take' p l (Sum.inr kmin) ((hl.2 _).2 (Finset.mem_univ _))] at hle
    · apply Finset.le_inf'
      intro k' hk'
      rw [ttm56_start_eq_sum_take' p l (Sum.inr k') ((hl.2 _).2 (Finset.mem_univ _))]
      have h1 : l.take (l.idxOf (Sum.inr k')) =
          l.take (l.idxOf (Sum.inr kmin)) ++
          (l.drop (l.idxOf (Sum.inr kmin))).take (l.idxOf (Sum.inr k') - l.idxOf (Sum.inr kmin)) := by
        rw [← List.take_add, Nat.add_sub_of_le (hkmin_min k' hk')]
      rw [h1, List.map_append, List.sum_append]
      have hnn : 0 ≤ (((l.drop (l.idxOf (Sum.inr kmin))).take
          (l.idxOf (Sum.inr k') - l.idxOf (Sum.inr kmin))).map p).sum :=
        List.sum_nonneg (by intro x hx; rw [List.mem_map] at hx; obtain ⟨j, _, rfl⟩ := hx; exact hp j)
      linarith
  · ext k''
    rw [bPrefSet, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨_, hlt⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      have hle_ac : aCount l k'' ≤ aCount l k := by
        rw [← hac_eq]; exact aCount_mono l hlt.le
      by_contra hnot_lt
      have heq_ac : aCount l k = aCount l k'' := le_antisymm (not_lt.1 hnot_lt) hle_ac
      have hk''_mem : k'' ∈ bBlock l k := by
        rw [bBlock, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (sameBBlock_iff_aCount_eq l hl k k'').2 heq_ac⟩
      have := hkmin_min k'' hk''_mem
      omega
    · rintro ⟨_, hlt_ac⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hnot_lt
      have hge : l.idxOf (Sum.inr kmin) ≤ l.idxOf (Sum.inr k'') := not_lt.1 hnot_lt
      have := aCount_mono l hge
      omega

open Classical in
lemma blockEnd_eq_max_bBlock {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (l : List (Job nA nB)) (hl : IsSchedule Finset.univ l) (k : Fin nB) :
    ∃ kmax ∈ bBlock l k,
      (∀ k' ∈ bBlock l k, l.idxOf (Sum.inr k') ≤ l.idxOf (Sum.inr kmax)) ∧
      blockEnd p l k = ((l.take (l.idxOf (Sum.inr kmax) + 1)).map p).sum ∧
      (aPrefSet l (l.idxOf (Sum.inr kmax) + 1)).card = aCount l k ∧
      bPrefSet l (l.idxOf (Sum.inr kmax) + 1) =
        Finset.univ.filter (fun k'' => aCount l k'' ≤ aCount l k) := by
  obtain ⟨kmax, hkmax_mem, hkmax_max⟩ :=
    Finset.exists_max_image (bBlock l k) (fun k' => l.idxOf (Sum.inr k')) ⟨k, mem_bBlock_self l k⟩
  have hac_eq : aCount l kmax = aCount l k := by
    have hkmax_same : SameBBlock l k kmax := (Finset.mem_filter.1 hkmax_mem).2
    exact ((sameBBlock_iff_aCount_eq l hl k kmax).1 hkmax_same).symm
  refine ⟨kmax, hkmax_mem, hkmax_max, ?_, ?_, ?_⟩
  · unfold blockEnd
    apply le_antisymm
    · apply Finset.sup'_le
      intro k' hk'
      rw [ttm56_ct_eq_sum_take']
      have h1 : l.take (l.idxOf (Sum.inr kmax) + 1) =
          l.take (l.idxOf (Sum.inr k') + 1) ++
          (l.drop (l.idxOf (Sum.inr k') + 1)).take
            ((l.idxOf (Sum.inr kmax) + 1) - (l.idxOf (Sum.inr k') + 1)) := by
        rw [← List.take_add, Nat.add_sub_of_le (Nat.add_le_add_right (hkmax_max k' hk') 1)]
      rw [h1, List.map_append, List.sum_append]
      have hnn : 0 ≤ (((l.drop (l.idxOf (Sum.inr k') + 1)).take
          ((l.idxOf (Sum.inr kmax) + 1) - (l.idxOf (Sum.inr k') + 1))).map p).sum :=
        List.sum_nonneg (by intro x hx; rw [List.mem_map] at hx; obtain ⟨j, _, rfl⟩ := hx; exact hp j)
      linarith
    · have hle := Finset.le_sup' (fun k' => completionTime p l (Sum.inr k')) hkmax_mem
      rwa [ttm56_ct_eq_sum_take'] at hle
  · rw [aPrefSet_inr_succ l hl kmax]; exact hac_eq
  · ext k''
    rw [bPrefSet, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨_, hlt⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hac_eq]
      exact aCount_mono l (by omega)
    · rintro ⟨_, hle_ac⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      by_cases heq_ac : aCount l k'' = aCount l k
      · have hk''_mem : k'' ∈ bBlock l k := by
          rw [bBlock, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, (sameBBlock_iff_aCount_eq l hl k k'').2 heq_ac.symm⟩
        have := hkmax_max k'' hk''_mem
        omega
      · have hlt_ac : aCount l k'' < aCount l kmax := by omega
        by_contra hnot_lt
        have hge : l.idxOf (Sum.inr kmax) ≤ l.idxOf (Sum.inr k'') := by omega
        have := aCount_mono l hge
        omega

open Classical in
theorem solution {nA nB : ℕ} (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (_hfeas : IsFeasibleInstance p fB Q) (σstar σ' : List (TwoAgentSched.MaxMax.Job nA nB))
    (hstar : IsOptimal p fB Q σstar) (h' : IsOptimal p fB Q σ') :
    (∀ k : Fin nB, bBlock σstar k = bBlock σ' k) ∧
      ∀ k : Fin nB, blockStart p σstar k = blockStart p σ' k ∧
        blockEnd p σstar k = blockEnd p σ' k := by
  have hp0 : ∀ j, 0 ≤ p j := fun j => (hp j).le
  have hac : ∀ k : Fin nB, aCount σstar k = aCount σ' k :=
    fun k => opt_aCount_eq p hp fB hfB Q σstar σ' hstar h' k
  refine ⟨fun k => ?_, fun k => ⟨?_, ?_⟩⟩
  · ext k'
    rw [bBlock, bBlock, Finset.mem_filter, Finset.mem_filter,
      sameBBlock_iff_aCount_eq σstar hstar.1.1 k k',
      sameBBlock_iff_aCount_eq σ' h'.1.1 k k', hac k, hac k']
  · obtain ⟨kmin₁, _, _, hstart₁, hac₁, hb₁⟩ := blockStart_eq_min_bBlock p hp0 σstar hstar.1.1 k
    obtain ⟨kmin₂, _, _, hstart₂, hac₂, hb₂⟩ := blockStart_eq_min_bBlock p hp0 σ' h'.1.1 k
    rw [hstart₁, hstart₂]
    have hb_eq : bPrefSet σstar (σstar.idxOf (Sum.inr kmin₁)) =
        bPrefSet σ' (σ'.idxOf (Sum.inr kmin₂)) := by
      rw [hb₁, hb₂]
      ext k''; simp [hac]
    apply le_antisymm
    · apply opt_sum_take_le p hp fB hfB Q σstar σ' hstar h'
      · change aCount σstar kmin₁ ≤ aCount σ' kmin₂
        rw [hac₁, hac₂, hac k]
      · exact hb_eq.subset
    · apply opt_sum_take_le p hp fB hfB Q σ' σstar h' hstar
      · change aCount σ' kmin₂ ≤ aCount σstar kmin₁
        rw [hac₁, hac₂, hac k]
      · exact hb_eq.symm.subset
  · obtain ⟨kmax₁, _, _, hend₁, hac₁, hb₁⟩ := blockEnd_eq_max_bBlock p hp0 σstar hstar.1.1 k
    obtain ⟨kmax₂, _, _, hend₂, hac₂, hb₂⟩ := blockEnd_eq_max_bBlock p hp0 σ' h'.1.1 k
    rw [hend₁, hend₂]
    have hb_eq : bPrefSet σstar (σstar.idxOf (Sum.inr kmax₁) + 1) =
        bPrefSet σ' (σ'.idxOf (Sum.inr kmax₂) + 1) := by
      rw [hb₁, hb₂]
      ext k''; simp [hac]
    apply le_antisymm
    · apply opt_sum_take_le p hp fB hfB Q σstar σ' hstar h'
      · rw [hac₁, hac₂, hac k]
      · exact hb_eq.subset
    · apply opt_sum_take_le p hp fB hfB Q σ' σstar h' hstar
      · rw [hac₁, hac₂, hac k]
      · exact hb_eq.symm.subset

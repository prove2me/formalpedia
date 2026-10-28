-- Prove2me | solution 1 for TwoAgentSched.ParetoTotal.theorem_11_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:29:14.304594+00:00
-- url     : https://prove2.me/submissions/1319a039-f25a-4446-8819-97cd90d2e954

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
import Definitions.Def_TwoAgentSched_ParetoTotal_Pareto
import Theorems.Thm_TwoAgentSched_TotalMax_theorem_5_5
import Theorems.Thm_TwoAgentSched_ParetoTotal_lemma_11_5

set_option autoImplicit false
open TwoAgentSched.ParetoTotal TwoAgentSched.TotalMax TwoAgentSched.MaxMax MooreLateJobs.Shared

section generic
variable {ι : Type*} [DecidableEq ι] (p : ι → ℝ)

lemma pt116_ca_append_left (l₁ l₂ : List ι) (m : ℕ) (hm : m < l₁.length) :
    completionAt p (l₁ ++ l₂) m = completionAt p l₁ m := by
  unfold completionAt
  rw [List.take_append_of_le_length (by omega)]

lemma pt116_ct_append_left (l₁ l₂ : List ι) (x : ι) (hx : x ∈ l₁) :
    completionTime p (l₁ ++ l₂) x = completionTime p l₁ x := by
  unfold completionTime
  rw [List.idxOf_append_of_mem hx]
  exact pt116_ca_append_left p l₁ l₂ _ (List.idxOf_lt_length_iff.mpr hx)

lemma pt116_ca_last (l : List ι) (z : ι) :
    completionAt p (l ++ [z]) l.length = ((l ++ [z]).map p).sum := by
  unfold completionAt
  have h1 : (l ++ [z]).take (l.length + 1) = l ++ [z] := List.take_of_length_le (by simp)
  rw [h1]

lemma pt116_ct_last (l : List ι) (z : ι) (hz : z ∉ l) :
    completionTime p (l ++ [z]) z = ((l ++ [z]).map p).sum := by
  unfold completionTime
  have h1 : (l ++ [z]).idxOf z = l.length := by
    rw [List.idxOf_append_of_notMem hz]; simp
  rw [h1]
  exact pt116_ca_last p l z

lemma pt116_ct_erase_le (hp : ∀ j, 0 ≤ p j) (l : List ι) (hnd : l.Nodup) (z x : ι)
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
  · rw [pt116_ct_append_left p a b x hxa, pt116_ct_append_left p a (z :: b) x hxa]
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

lemma pt116_last_cost (l : List ι) (hnd : l.Nodup) (hne : l ≠ []) :
    ∃ y ∈ l, completionTime p l y = (l.map p).sum := by
  obtain ⟨L, y, hL⟩ := (List.eq_nil_or_concat l).resolve_left hne
  rw [List.concat_eq_append] at hL
  subst hL
  refine ⟨y, by simp, ?_⟩
  have hy : y ∉ L := fun h => (List.nodup_append.1 hnd).2.2 y h y (by simp) rfl
  exact pt116_ct_last p L y hy

lemma pt116_erase_ex (hp : ∀ j, 0 ≤ p j) (l : List ι) (hnd : l.Nodup) (z : ι) (hz : z ∈ l) :
    ∃ l'', l.Perm (l'' ++ [z]) ∧
      ∀ x ∈ l'', x ∈ l ∧ x ≠ z ∧ completionTime p l'' x ≤ completionTime p l x := by
  refine ⟨l.erase z, ?_, fun x hx => ?_⟩
  · exact (List.perm_cons_erase hz).trans (List.perm_append_singleton z _).symm
  · rw [hnd.mem_erase_iff] at hx
    exact ⟨hx.2, hx.1, pt116_ct_erase_le p hp l hnd z x hz hx.2 hx.1⟩

lemma pt116_sum_take_le_of_subset (hp : ∀ j, 0 ≤ p j) (l₁ l₂ : List ι)
    (hnd₁ : l₁.Nodup) (hnd₂ : l₂.Nodup) (m₁ m₂ : ℕ)
    (hsub : ∀ x, x ∈ l₁.take m₁ → x ∈ l₂.take m₂) :
    ((l₁.take m₁).map p).sum ≤ ((l₂.take m₂).map p).sum := by
  rw [← List.sum_toFinset p hnd₁.take, ← List.sum_toFinset p hnd₂.take]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact hsub x hx
  · intro x _ _
    exact hp x

lemma pt116_ct_le_of_prefix_subset (hp : ∀ j, 0 ≤ p j) (l₁ l₂ : List ι)
    (hnd₁ : l₁.Nodup) (hnd₂ : l₂.Nodup) (x₁ x₂ : ι)
    (hsub : ∀ x, x ∈ l₁ → l₁.idxOf x ≤ l₁.idxOf x₁ → x ∈ l₂ ∧ l₂.idxOf x ≤ l₂.idxOf x₂) :
    completionTime p l₁ x₁ ≤ completionTime p l₂ x₂ := by
  unfold completionTime completionAt
  apply pt116_sum_take_le_of_subset p hp l₁ l₂ hnd₁ hnd₂
  intro x hx
  have hx₁ : x ∈ l₁ := List.mem_of_mem_take hx
  rw [List.mem_take_iff_idxOf_lt hx₁] at hx
  have ⟨hx₂, hle₂⟩ := hsub x hx₁ (by omega)
  rw [List.mem_take_iff_idxOf_lt hx₂]
  omega

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

lemma pt116_beq_eq {nA nB : ℕ} (a z : Job nA nB) :
    @BEq.beq (Job nA nB) instBEqOfDecidableEq a z = (a == z) := by
  change decide (a = z) = (a == z)
  by_cases h : a = z
  · subst h; rw [decide_eq_true rfl, beq_self_eq_true]
  · rw [decide_eq_false h, beq_false_of_ne h]

lemma pt116_idxOf_eq {nA nB : ℕ} (l : List (Job nA nB)) (z : Job nA nB) :
    @List.idxOf (Job nA nB) instBEqOfDecidableEq z l = l.idxOf z := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.idxOf_cons, pt116_beq_eq, ih]

lemma pt116_ct_le_of_prefix_subset' {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (l₁ l₂ : List (Job nA nB)) (hnd₁ : l₁.Nodup) (hnd₂ : l₂.Nodup) (x₁ x₂ : Job nA nB)
    (hsub : ∀ x, x ∈ l₁ → l₁.idxOf x ≤ l₁.idxOf x₁ → x ∈ l₂ ∧ l₂.idxOf x ≤ l₂.idxOf x₂) :
    completionTime p l₁ x₁ ≤ completionTime p l₂ x₂ := by
  apply pt116_ct_le_of_prefix_subset p hp l₁ l₂ hnd₁ hnd₂ x₁ x₂
  intro x hx₁ hle₁
  rw [pt116_idxOf_eq, pt116_idxOf_eq] at hle₁ ⊢
  exact hsub x hx₁ hle₁

lemma pt116_rule_append_iff {nA nB : ℕ} (p : Job nA nB → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (σ : List (Job nA nB)) (z : Job nA nB) :
    IsFig1Seq p fB Q (σ ++ [z]) ↔
      IsFig1Seq p fB Q σ ∧
      ((∃ k : Fin nB, Sum.inr k ∈ (σ ++ [z]).toFinset ∧ fB k ((σ ++ [z]).map p).sum ≤ Q) →
        ∃ k : Fin nB, z = Sum.inr k ∧ fB k ((σ ++ [z]).map p).sum ≤ Q) ∧
      ((¬ ∃ k : Fin nB, Sum.inr k ∈ (σ ++ [z]).toFinset ∧ fB k ((σ ++ [z]).map p).sum ≤ Q) →
        ∃ h : Fin nA, z = Sum.inl h ∧
          ∀ h' : Fin nA, Sum.inl h' ∈ (σ ++ [z]).toFinset → p (Sum.inl h') ≤ p (Sum.inl h)) := by
  have hT : ∀ m, m < σ.length → (σ ++ [z]).take (m + 1) = σ.take (m + 1) :=
    fun m hm => List.take_append_of_le_length (by omega)
  have hCA : ∀ m, m < σ.length → completionAt p (σ ++ [z]) m = completionAt p σ m :=
    fun m hm => pt116_ca_append_left p σ [z] m hm
  have hTlast : (σ ++ [z]).take (σ.length + 1) = σ ++ [z] :=
    List.take_of_length_le (by simp)
  have hCAlast : completionAt p (σ ++ [z]) σ.length = ((σ ++ [z]).map p).sum :=
    pt116_ca_last p σ z
  have hlen : (σ ++ [z]).length = σ.length + 1 := by simp
  constructor
  · intro H
    refine ⟨fun m hm => ?_, ?_⟩
    · have := H m (by omega)
      have hg : (σ ++ [z])[m]'(by omega) = σ[m] := List.getElem_append_left hm
      rw [hg, hT m hm, hCA m hm] at this
      exact this
    · have := H σ.length (by omega)
      have hg : (σ ++ [z])[σ.length]'(by omega) = z := by simp
      rw [hg, hTlast, hCAlast] at this
      exact this
  · rintro ⟨H, hlast⟩ m hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 (hlen ▸ hm) with hm' | hm'
    · have := H m hm'
      have hg : (σ ++ [z])[m]'(by omega) = σ[m] := List.getElem_append_left hm'
      rw [hg, hT m hm', hCA m hm']
      exact this
    · subst hm'
      have hg : (σ ++ [z])[σ.length]'(by omega) = z := by simp
      rw [hg, hTlast, hCAlast]
      exact hlast

lemma aFollowsSPT_append_singleton {nA nB : ℕ} (p : Job nA nB → ℝ)
    (σ0 : List (Job nA nB)) (z : Job nA nB)
    (hspt0 : AFollowsSPT p σ0)
    (hz : ∀ h h' : Fin nA, Sum.inl h ∈ σ0 → z = Sum.inl h' →
      p (Sum.inl h) < p (Sum.inl h') ∨ (p (Sum.inl h) = p (Sum.inl h') ∧ h < h')) :
    AFollowsSPT p (σ0 ++ [z]) := by
  unfold AFollowsSPT at hspt0 ⊢
  rw [List.pairwise_append]
  refine ⟨hspt0, List.pairwise_singleton _ z, ?_⟩
  intro x hx y hy h h' rfl rfl
  rw [List.mem_singleton] at hy
  exact hz h h' hx hy.symm

def pt116FeasB {nA nB : ℕ} (p : Job nA nB → ℝ) (fB : Fin nB → ℝ → ℝ) (Q : ℝ)
    (l : List (Job nA nB)) : Prop :=
  ∀ k : Fin nB, Sum.inr k ∈ l → fB k (completionTime p l (Sum.inr k)) ≤ Q

lemma pt116_build {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 ≤ p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ) :
    ∀ n : ℕ, ∀ l' : List (Job nA nB), l'.length = n → l'.Nodup → pt116FeasB p fB Q l' →
      ∃ σ : List (Job nA nB), σ.Perm l' ∧ IsFig1Seq p fB Q σ ∧ AFollowsSPT p σ := by
  intro n
  induction n with
  | zero =>
    intro l' hlen _ _
    have : l' = [] := List.length_eq_zero_iff.1 hlen
    subst this
    exact ⟨[], List.Perm.refl _, fun m hm => absurd hm (by simp), List.Pairwise.nil⟩
  | succ n ih =>
    intro l' hlen hnd hfeas
    have hne : l' ≠ [] := by intro h; subst h; simp at hlen
    have hz : ∃ z ∈ l',
        ((∃ k : Fin nB, Sum.inr k ∈ l' ∧ fB k (l'.map p).sum ≤ Q) →
          ∃ k : Fin nB, z = Sum.inr k ∧ fB k (l'.map p).sum ≤ Q) ∧
        ((¬ ∃ k : Fin nB, Sum.inr k ∈ l' ∧ fB k (l'.map p).sum ≤ Q) →
          ∃ h : Fin nA, z = Sum.inl h ∧
            ∀ h' : Fin nA, Sum.inl h' ∈ l' → p (Sum.inl h') ≤ p (Sum.inl h)) ∧
        (∀ h h' : Fin nA, Sum.inl h ∈ l' → z = Sum.inl h' → h ≠ h' →
          p (Sum.inl h) < p (Sum.inl h') ∨ (p (Sum.inl h) = p (Sum.inl h') ∧ h < h')) := by
      classical
      by_cases hel : ∃ k : Fin nB, Sum.inr k ∈ l' ∧ fB k (l'.map p).sum ≤ Q
      · obtain ⟨k, hk, hle⟩ := hel
        refine ⟨Sum.inr k, hk, fun _ => ⟨k, rfl, hle⟩, fun hn => absurd ⟨k, hk, hle⟩ hn, ?_⟩
        intro _ _ _ heq
        exact absurd heq (by simp)
      · obtain ⟨y, hy, hyc⟩ := pt116_last_cost p l' hnd hne
        rcases y with h_last | k_last
        · set A : Finset (Fin nA) := Finset.univ.filter (fun h : Fin nA => Sum.inl h ∈ l')
          have h_last_mem : h_last ∈ A := by simp [A, hy]
          obtain ⟨h1, hh1, hmax1⟩ :=
            Finset.exists_max_image A (fun h => p (Sum.inl h)) ⟨h_last, h_last_mem⟩
          set Amax : Finset (Fin nA) := A.filter (fun h => p (Sum.inl h) = p (Sum.inl h1))
          have hh1_max : h1 ∈ Amax := by simp [Amax, hh1]
          obtain ⟨h0, hh0, hmax0⟩ :=
            Finset.exists_max_image Amax (fun h => h) ⟨h1, hh1_max⟩
          have hh0_A : h0 ∈ A := (Finset.mem_filter.1 hh0).1
          have hh0_p : p (Sum.inl h0) = p (Sum.inl h1) := (Finset.mem_filter.1 hh0).2
          have hh0_in : (Sum.inl h0 : Job nA nB) ∈ l' := (Finset.mem_filter.1 hh0_A).2
          have hp_le : ∀ h' : Fin nA, Sum.inl h' ∈ l' → p (Sum.inl h') ≤ p (Sum.inl h0) := by
            intro h' hh'
            rw [hh0_p]
            exact hmax1 h' (by simp [A, hh'])
          refine ⟨Sum.inl h0, hh0_in, fun hh => absurd hh hel,
            fun _ => ⟨h0, rfl, hp_le⟩, ?_⟩
          intro h h' hh_in hz_eq hne_hh'
          have hh'_eq : h0 = h' := Sum.inl_injective hz_eq
          subst hh'_eq
          have hle := hp_le h hh_in
          by_cases heq_p : p (Sum.inl h) = p (Sum.inl h0)
          · right
            refine ⟨heq_p, ?_⟩
            have hh_Amax : h ∈ Amax := by
              simp [Amax, A, hh_in, heq_p, hh0_p]
            exact lt_of_le_of_ne (hmax0 h hh_Amax) hne_hh'
          · left
            exact lt_of_le_of_ne hle heq_p
        · exfalso
          have := hfeas k_last hy
          rw [hyc] at this
          exact hel ⟨k_last, hy, this⟩
    obtain ⟨z, hzl, hz1, hz2, hz3⟩ := hz
    obtain ⟨l'', hperm0, hl''⟩ := pt116_erase_ex p hp l' hnd z hzl
    have hlen'' : l''.length = n := by
      have := hperm0.length_eq
      simp at this
      omega
    have hnd'' : l''.Nodup :=
      (List.nodup_append.1 (hperm0.nodup_iff.1 hnd)).1
    have hfeas'' : pt116FeasB p fB Q l'' := fun k hk =>
      (hfB k (hl'' _ hk).2.2).trans (hfeas k (hl'' _ hk).1)
    obtain ⟨σ'', hσperm, hσrule, hσspt⟩ := ih l'' hlen'' hnd'' hfeas''
    have hperm : (σ'' ++ [z]).Perm l' :=
      ((hσperm.append_right [z]).trans hperm0.symm)
    have hsum : ((σ'' ++ [z]).map p).sum = (l'.map p).sum := (hperm.map p).sum_eq
    have hmem : ∀ x, x ∈ (σ'' ++ [z]).toFinset ↔ x ∈ l' := fun x => by
      rw [List.mem_toFinset]; exact hperm.mem_iff
    have hspt : AFollowsSPT p (σ'' ++ [z]) := by
      apply aFollowsSPT_append_singleton p σ'' z hσspt
      intro h h' hh_σ'' hz_eq
      have hh_l'' : (Sum.inl h : Job nA nB) ∈ l'' := hσperm.mem_iff.1 hh_σ''
      have ⟨hh_l', hne_z, _⟩ := hl'' (Sum.inl h) hh_l''
      have hne_hh' : h ≠ h' := by
        intro heq; subst heq; exact hne_z hz_eq.symm
      exact hz3 h h' hh_l' hz_eq hne_hh'
    refine ⟨σ'' ++ [z], hperm, (pt116_rule_append_iff p fB Q σ'' z).2 ⟨hσrule, ?_, ?_⟩, hspt⟩
    · intro hex
      obtain ⟨k, hk1, hk2⟩ := hex
      rw [hmem] at hk1
      rw [hsum] at hk2 ⊢
      exact hz1 ⟨k, hk1, hk2⟩
    · intro hnot
      have hel : ¬ ∃ k : Fin nB, Sum.inr k ∈ l' ∧ fB k (l'.map p).sum ≤ Q := by
        rintro ⟨k, hk1, hk2⟩
        exact hnot ⟨k, (hmem _).2 hk1, by rw [hsum]; exact hk2⟩
      obtain ⟨h, hh1, hh2⟩ := hz2 hel
      exact ⟨h, hh1, fun h' hh' => hh2 h' ((hmem _).1 hh')⟩

lemma spt_idxOf_lt_imp {nA nB : ℕ} (p : Job nA nB → ℝ) (l : List (Job nA nB))
    (hspt : AFollowsSPT p l) (h j : Fin nA) (hh : Sum.inl h ∈ l) (hj : Sum.inl j ∈ l)
    (hlt : l.idxOf (Sum.inl h) < l.idxOf (Sum.inl j)) :
    p (Sum.inl h) < p (Sum.inl j) ∨ (p (Sum.inl h) = p (Sum.inl j) ∧ h < j) := by
  rw [AFollowsSPT, List.pairwise_iff_getElem] at hspt
  have hi : l.idxOf (Sum.inl h) < l.length := List.idxOf_lt_length_iff.2 hh
  have hj' : l.idxOf (Sum.inl j) < l.length := List.idxOf_lt_length_iff.2 hj
  exact hspt (l.idxOf (Sum.inl h)) (l.idxOf (Sum.inl j)) hi hj' hlt h j
    (List.getElem_idxOf _) (List.getElem_idxOf _)

lemma spt_idxOf_le_iff {nA nB : ℕ} (p : Job nA nB → ℝ) (σ σ' : List (Job nA nB))
    (hσ : IsSchedule Finset.univ σ) (hσ' : IsSchedule Finset.univ σ')
    (hspt : AFollowsSPT p σ) (hspt' : AFollowsSPT p σ') (h j : Fin nA)
    (hle : σ.idxOf (Sum.inl h) ≤ σ.idxOf (Sum.inl j)) :
    σ'.idxOf (Sum.inl h) ≤ σ'.idxOf (Sum.inl j) := by
  by_contra hcon
  have hlt' : σ'.idxOf (Sum.inl j) < σ'.idxOf (Sum.inl h) := not_le.1 hcon
  have hne : (Sum.inl h : Job nA nB) ≠ Sum.inl j := by
    intro heq; rw [heq] at hlt'; exact lt_irrefl _ hlt'
  have hhσ : (Sum.inl h : Job nA nB) ∈ σ := (hσ.2 _).2 (Finset.mem_univ _)
  have hjσ : (Sum.inl j : Job nA nB) ∈ σ := (hσ.2 _).2 (Finset.mem_univ _)
  have hhσ' : (Sum.inl h : Job nA nB) ∈ σ' := (hσ'.2 _).2 (Finset.mem_univ _)
  have hjσ' : (Sum.inl j : Job nA nB) ∈ σ' := (hσ'.2 _).2 (Finset.mem_univ _)
  have hidx_ne : σ.idxOf (Sum.inl h) ≠ σ.idxOf (Sum.inl j) :=
    fun heq => hne ((List.idxOf_inj hhσ).1 heq)
  have hlt : σ.idxOf (Sum.inl h) < σ.idxOf (Sum.inl j) := lt_of_le_of_ne hle hidx_ne
  have h1 := spt_idxOf_lt_imp p σ hspt h j hhσ hjσ hlt
  have h2 := spt_idxOf_lt_imp p σ' hspt' j h hjσ' hhσ' hlt'
  rcases h1 with h1 | ⟨h1a, h1b⟩ <;> rcases h2 with h2 | ⟨h2a, h2b⟩
  · linarith
  · linarith
  · linarith
  · exact lt_asymm h1b h2b

instance {nA nB : ℕ} (σ : List (Job nA nB)) (k : Fin nB) (j : Fin nA) :
    Decidable (BPrecedesA σ k j) :=
  inferInstanceAs (Decidable (_ < _))

def bBeforeASet {nA nB : ℕ} (σ : List (Job nA nB)) : Finset (Fin nB × Fin nA) :=
  Finset.univ.filter (fun kj => BPrecedesA σ kj.1 kj.2)

lemma totalCompletionA_le_of_bBeforeASet_subset {nA nB : ℕ} (p : Job nA nB → ℝ)
    (hp : ∀ j, 0 < p j) (σ₁ σ₂ : List (Job nA nB))
    (hσ₁ : IsSchedule Finset.univ σ₁) (hσ₂ : IsSchedule Finset.univ σ₂)
    (hspt₁ : AFollowsSPT p σ₁) (hspt₂ : AFollowsSPT p σ₂)
    (hsub : bBeforeASet σ₁ ⊆ bBeforeASet σ₂) :
    totalCompletionA p σ₁ ≤ totalCompletionA p σ₂ := by
  have hp0 : ∀ x, 0 ≤ p x := fun x => (hp x).le
  unfold totalCompletionA
  apply Finset.sum_le_sum
  intro j _
  apply pt116_ct_le_of_prefix_subset' p hp0 σ₁ σ₂ hσ₁.1 hσ₂.1 (Sum.inl j) (Sum.inl j)
  intro x _ hle
  refine ⟨(hσ₂.2 x).2 (Finset.mem_univ x), ?_⟩
  rcases x with h | k
  · exact spt_idxOf_le_iff p σ₁ σ₂ hσ₁ hσ₂ hspt₁ hspt₂ h j hle
  · have hne : (Sum.inr k : Job nA nB) ≠ Sum.inl j := by simp
    have hkσ₁ : (Sum.inr k : Job nA nB) ∈ σ₁ := (hσ₁.2 _).2 (Finset.mem_univ _)
    have hidx_ne : σ₁.idxOf (Sum.inr k) ≠ σ₁.idxOf (Sum.inl j) :=
      fun heq => hne ((List.idxOf_inj hkσ₁).1 heq)
    have hlt : BPrecedesA σ₁ k j := lt_of_le_of_ne hle hidx_ne
    have hmem₁ : (k, j) ∈ bBeforeASet σ₁ := by
      simp [bBeforeASet, hlt]
    have hmem₂ := hsub hmem₁
    rw [bBeforeASet, Finset.mem_filter] at hmem₂
    have hlt₂ : BPrecedesA σ₂ k j := hmem₂.2
    unfold BPrecedesA at hlt₂
    omega

lemma exists_canonical_for_ndPair {nA nB : ℕ} (hB : 0 < nB) (p : Job nA nB → ℝ)
    (hp : ∀ j, 0 < p j) (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k))
    (q : ℝ × ℝ) (hq : q ∈ ndPairs hB p fB) :
    ∃ σ : List (Job nA nB),
      IsNondominated hB p fB σ ∧
      IsOptimal p fB q.2 σ ∧
      AFollowsSPT p σ ∧
      totalCompletionA p σ = q.1 ∧
      maxCostB hB p fB σ = q.2 := by
  have hp0 : ∀ x, 0 ≤ p x := fun x => (hp x).le
  obtain ⟨l0, hl0_nd, hq_eq⟩ := hq
  have hl0_A : totalCompletionA p l0 = q.1 := by rw [hq_eq]
  have hl0_B : maxCostB hB p fB l0 = q.2 := by rw [hq_eq]
  have hl0_feas : IsFeasible p fB q.2 l0 := by
    refine ⟨hl0_nd.1, fun k => ?_⟩
    rw [← hl0_B]
    exact Finset.le_sup' (fun k => fB k (completionTime p l0 (Sum.inr k))) (Finset.mem_univ k)
  obtain ⟨σ, hσperm, hσfig1, hσspt⟩ :=
    pt116_build p hp0 fB hfB q.2 l0.length l0 rfl hl0_nd.1.1 (fun k _ => hl0_feas.2 k)
  have hσ_sched : IsSchedule Finset.univ σ :=
    ⟨hσperm.nodup_iff.2 hl0_nd.1.1, fun x => by rw [hσperm.mem_iff, hl0_nd.1.2 x]⟩
  have hσ_opt : IsOptimal p fB q.2 σ :=
    (theorem_5_5 p hp fB hfB q.2).1 ⟨l0, hl0_feas⟩ σ hσ_sched hσfig1
  have hσ_Ale : totalCompletionA p σ ≤ q.1 := by
    rw [← hl0_A]
    exact hσ_opt.2 l0 hl0_feas
  have hσ_Ble : maxCostB hB p fB σ ≤ q.2 :=
    Finset.sup'_le _ _ (fun k _ => hσ_opt.1.2 k)
  have hσ_Aeq : totalCompletionA p σ = q.1 := by
    by_contra hne
    have hlt : totalCompletionA p σ < q.1 := lt_of_le_of_ne hσ_Ale hne
    exact hl0_nd.2 ⟨σ, hσ_sched, by linarith, by linarith, Or.inl (by linarith)⟩
  have hσ_Beq : maxCostB hB p fB σ = q.2 := by
    by_contra hne
    have hlt : maxCostB hB p fB σ < q.2 := lt_of_le_of_ne hσ_Ble hne
    exact hl0_nd.2 ⟨σ, hσ_sched, by linarith, by linarith, Or.inr (by linarith)⟩
  have hσ_nd : IsNondominated hB p fB σ := by
    refine ⟨hσ_sched, ?_⟩
    rintro ⟨l', hl', h1, h2, h3⟩
    rw [hσ_Aeq, ← hl0_A] at h1 h3
    rw [hσ_Beq, ← hl0_B] at h2 h3
    exact hl0_nd.2 ⟨l', hl', h1, h2, h3⟩
  exact ⟨σ, hσ_nd, hσ_opt, hσspt, hσ_Aeq, hσ_Beq⟩

theorem solution {nA nB : ℕ} (hB : 0 < nB) (p : TwoAgentSched.MaxMax.Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) :
    (ndPairs hB p fB).encard ≤ ((nA * nB + 1 : ℕ) : ℕ∞) := by
  classical
  let f : ℝ × ℝ → ℕ := fun q =>
    if hq : q ∈ ndPairs hB p fB then
      (bBeforeASet (Classical.choose (exists_canonical_for_ndPair hB p hp fB hfB q hq))).card
    else 0
  have hmaps : Set.MapsTo f (ndPairs hB p fB) {i : ℕ | i < nA * nB + 1} := by
    intro q hq
    simp only [Set.mem_setOf_eq, f, dif_pos hq]
    have hle : (bBeforeASet (Classical.choose (exists_canonical_for_ndPair hB p hp fB hfB q hq))).card ≤
        (Finset.univ : Finset (Fin nB × Fin nA)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hle
    rw [Nat.mul_comm nB nA] at hle
    omega
  have hinj : Set.InjOn f (ndPairs hB p fB) := by
    intro q₁ hq₁ q₂ hq₂ hfeq
    by_contra hne
    simp only [f, dif_pos hq₁, dif_pos hq₂] at hfeq
    set σ₁ := Classical.choose (exists_canonical_for_ndPair hB p hp fB hfB q₁ hq₁)
    obtain ⟨hσ₁_nd, hσ₁_opt, hσ₁_spt, hσ₁_A, hσ₁_B⟩ :=
      Classical.choose_spec (exists_canonical_for_ndPair hB p hp fB hfB q₁ hq₁)
    set σ₂ := Classical.choose (exists_canonical_for_ndPair hB p hp fB hfB q₂ hq₂)
    obtain ⟨hσ₂_nd, hσ₂_opt, hσ₂_spt, hσ₂_A, hσ₂_B⟩ :=
      Classical.choose_spec (exists_canonical_for_ndPair hB p hp fB hfB q₂ hq₂)
    -- Since q₁ ≠ q₂ and both σ₁, σ₂ are nondominated, either q₁.2 > q₂.2 ∧ q₁.1 < q₂.1 or vice versa
    have hstrict : (q₂.2 < q₁.2 ∧ q₁.1 < q₂.1) ∨ (q₁.2 < q₂.2 ∧ q₂.1 < q₁.1) := by
      rcases lt_trichotomy q₁.2 q₂.2 with hBlt | hBeq | hBgt
      · right
        refine ⟨hBlt, ?_⟩
        rcases lt_trichotomy q₂.1 q₁.1 with hAlt | hAeq | hAgt
        · exact hAlt
        · exfalso
          exact hσ₂_nd.2 ⟨σ₁, hσ₁_nd.1, by linarith, by linarith, Or.inr (by linarith)⟩
        · exfalso
          exact hσ₂_nd.2 ⟨σ₁, hσ₁_nd.1, by linarith, by linarith, Or.inl (by linarith)⟩
      · rcases lt_trichotomy q₁.1 q₂.1 with hAlt | hAeq | hAgt
        · exfalso
          exact hσ₂_nd.2 ⟨σ₁, hσ₁_nd.1, by linarith, by linarith, Or.inl (by linarith)⟩
        · exfalso
          exact hne (Prod.ext hAeq hBeq)
        · exfalso
          exact hσ₁_nd.2 ⟨σ₂, hσ₂_nd.1, by linarith, by linarith, Or.inl (by linarith)⟩
      · left
        refine ⟨hBgt, ?_⟩
        rcases lt_trichotomy q₁.1 q₂.1 with hAlt | hAeq | hAgt
        · exact hAlt
        · exfalso
          exact hσ₁_nd.2 ⟨σ₂, hσ₂_nd.1, by linarith, by linarith, Or.inr (by linarith)⟩
        · exfalso
          exact hσ₁_nd.2 ⟨σ₂, hσ₂_nd.1, by linarith, by linarith, Or.inl (by linarith)⟩
    rcases hstrict with ⟨hQlt, hAlt⟩ | ⟨hQlt, hAlt⟩
    · have hsub : bBeforeASet σ₁ ⊆ bBeforeASet σ₂ := by
        intro kj hkj
        rw [bBeforeASet, Finset.mem_filter] at hkj ⊢
        exact ⟨Finset.mem_univ _, lemma_11_5 p hp fB hfB q₁.2 q₂.2 hQlt σ₁ σ₂
          hσ₁_opt hσ₂_opt hσ₁_spt hσ₂_spt kj.1 kj.2 hkj.2⟩
      have heq_set : bBeforeASet σ₁ = bBeforeASet σ₂ :=
        Finset.eq_of_subset_of_card_le hsub (by omega)
      have htot_le : totalCompletionA p σ₂ ≤ totalCompletionA p σ₁ :=
        totalCompletionA_le_of_bBeforeASet_subset p hp σ₂ σ₁ hσ₂_nd.1 hσ₁_nd.1
          hσ₂_spt hσ₁_spt (heq_set.symm.subset)
      linarith
    · have hsub : bBeforeASet σ₂ ⊆ bBeforeASet σ₁ := by
        intro kj hkj
        rw [bBeforeASet, Finset.mem_filter] at hkj ⊢
        exact ⟨Finset.mem_univ _, lemma_11_5 p hp fB hfB q₂.2 q₁.2 hQlt σ₂ σ₁
          hσ₂_opt hσ₁_opt hσ₂_spt hσ₁_spt kj.1 kj.2 hkj.2⟩
      have heq_set : bBeforeASet σ₂ = bBeforeASet σ₁ :=
        Finset.eq_of_subset_of_card_le hsub (by omega)
      have htot_le : totalCompletionA p σ₁ ≤ totalCompletionA p σ₂ :=
        totalCompletionA_le_of_bBeforeASet_subset p hp σ₁ σ₂ hσ₁_nd.1 hσ₂_nd.1
          hσ₁_spt hσ₂_spt (heq_set.symm.subset)
      linarith
  have henc := Set.encard_le_encard_of_injOn hmaps hinj
  rwa [Set.Nat.encard_range (nA * nB + 1)] at henc

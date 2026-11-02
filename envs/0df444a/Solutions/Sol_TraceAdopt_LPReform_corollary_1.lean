-- Prove2me | solution 1 for TraceAdopt.LPReform.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:33:44.112119+00:00
-- url     : https://prove2.me/submissions/723954f9-901f-463d-a9fc-31920a64a78c

import Definitions.Def_TraceAdopt_LPReform_Model

namespace TraceAdopt.LPReform

theorem ta_ltm_mem (I : Instance) (S : Finset (Fin I.n ⊕ Fin I.m)) (v : Fin I.n ⊕ Fin I.m) :
    v ∈ ltmStep I S ↔ v ∈ S ∨ (v ∉ S ∧
      match v with
      | Sum.inl i => I.c i ≤ ∑ j ∈ Finset.univ.filter
          (fun j => Sum.inr j ∈ S ∧ i ∈ I.e j), I.r j i
      | Sum.inr j => I.θ j - 1 ≤
          (Finset.univ.filter (fun i => Sum.inl i ∈ S ∧ i ∈ I.e j)).card) := by
  classical
  unfold ltmStep
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · right; refine ⟨h1, ?_⟩
      cases v with
      | inl i => simpa using h2
      | inr j => simpa using h2
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · right; refine ⟨h1, ?_⟩
      cases v with
      | inl i => simpa using h2
      | inr j => simpa using h2

theorem ta_ltm_inl (I : Instance) (S : Finset (Fin I.n ⊕ Fin I.m)) (i : Fin I.n) :
    Sum.inl i ∈ ltmStep I S ↔ Sum.inl i ∈ S ∨ I.c i ≤ ∑ j ∈ Finset.univ.filter
          (fun j => Sum.inr j ∈ S ∧ i ∈ I.e j), I.r j i := by
  rw [ta_ltm_mem]
  tauto

theorem ta_ltm_inr (I : Instance) (S : Finset (Fin I.n ⊕ Fin I.m)) (j : Fin I.m) :
    Sum.inr j ∈ ltmStep I S ↔ Sum.inr j ∈ S ∨ I.θ j - 1 ≤
          (Finset.univ.filter (fun i => Sum.inl i ∈ S ∧ i ∈ I.e j)).card := by
  rw [ta_ltm_mem]
  tauto

theorem ta_step_mem (I : Instance) (S : Finset (Fin I.n)) (i : Fin I.n) :
    i ∈ step I S ↔ i ∈ S ∨ I.c i ≤ ∑ j ∈ Finset.univ.filter
      (fun j => i ∈ I.e j ∧ I.θ j - 1 ≤ (S ∩ I.e j).card), I.r j i := by
  unfold step
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

theorem ta_step_mono (I : Instance) {S U : Finset (Fin I.n)} (h : S ⊆ U) :
    step I S ⊆ step I U := by
  intro i hi
  rw [ta_step_mem] at hi ⊢
  rcases hi with hi | hi
  · exact Or.inl (h hi)
  · right
    refine le_trans hi (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _))
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.1, le_trans hj.2 (Finset.card_le_card (Finset.inter_subset_inter_right h))⟩

theorem ta_step_ext (I : Instance) (S : Finset (Fin I.n)) : S ⊆ step I S := by
  intro i hi; rw [ta_step_mem]; exact Or.inl hi

theorem ta_ltm_ext (I : Instance) (S : Finset (Fin I.n ⊕ Fin I.m)) : S ⊆ ltmStep I S := by
  intro v hv; rw [ta_ltm_mem]; exact Or.inl hv

theorem ta_iter_step_succ_sub (I : Instance) (S : Finset (Fin I.n)) (t : ℕ) :
    (step I)^[t] S ⊆ (step I)^[t+1] S := by
  rw [Function.iterate_succ_apply']
  exact ta_step_ext I _

theorem ta_iter_ltm_mono (I : Instance) (S : Finset (Fin I.n ⊕ Fin I.m)) {a b : ℕ}
    (h : a ≤ b) : (ltmStep I)^[a] S ⊆ (ltmStep I)^[b] S := by
  induction b with
  | zero => simp at h; subst h; exact le_rfl
  | succ b ih =>
    rcases Nat.of_le_succ h with h | h
    · rw [Function.iterate_succ_apply']
      exact (ih h).trans (ta_ltm_ext I _)
    · rw [h]

/-- The supplier activation set `J(S)`. -/
def taJ (I : Instance) (S : Finset (Fin I.n)) (j : Fin I.m) : Prop :=
  I.θ j - 1 ≤ (S ∩ I.e j).card

theorem ta_card_eq (I : Instance) (S' : Finset (Fin I.n ⊕ Fin I.m)) (S : Finset (Fin I.n))
    (hf : ∀ i, Sum.inl i ∈ S' ↔ i ∈ S) (j : Fin I.m) :
    (Finset.univ.filter (fun i => Sum.inl i ∈ S' ∧ i ∈ I.e j)).card = (S ∩ I.e j).card := by
  congr 1
  ext i
  simp [hf]

theorem ta_invariant (I : Instance) (hc : ∀ i, 0 < I.c i) (S₀ : Finset (Fin I.n)) (t : ℕ) :
    (∀ i, Sum.inl i ∈ (ltmStep I)^[2 * t] (liftSeeds I S₀) ↔ i ∈ (step I)^[t] S₀) ∧
    (∀ i, I.c i ≤ ∑ j ∈ Finset.univ.filter
        (fun j => Sum.inr j ∈ (ltmStep I)^[2 * t] (liftSeeds I S₀) ∧ i ∈ I.e j), I.r j i →
        i ∈ (step I)^[t] S₀) ∧
    (∀ j, Sum.inr j ∈ (ltmStep I)^[2 * t] (liftSeeds I S₀) → taJ I ((step I)^[t] S₀) j) := by
  induction t with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro i; simp [liftSeeds]
    · intro i h
      exfalso
      simp [liftSeeds] at h
      have := hc i
      omega
    · intro j h; simp [liftSeeds] at h
  | succ t ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    set S' := (ltmStep I)^[2 * t] (liftSeeds I S₀) with hS'
    set S := (step I)^[t] S₀ with hS
    -- time 2t+1
    have o1 : ∀ i, Sum.inl i ∈ ltmStep I S' ↔ i ∈ S := by
      intro i
      rw [ta_ltm_inl, h1]
      constructor
      · rintro (h | h)
        · exact h
        · exact h2 i h
      · intro h; exact Or.inl h
    have o2 : ∀ j, Sum.inr j ∈ ltmStep I S' ↔ taJ I S j := by
      intro j
      rw [ta_ltm_inr, ta_card_eq I S' S h1]
      constructor
      · rintro (h | h)
        · exact h3 j h
        · exact h
      · intro h; exact Or.inr h
    have e2 : 2 * (t + 1) = (2 * t + 1) + 1 := by ring
    have hS1 : (step I)^[t+1] S₀ = step I S := by
      rw [Function.iterate_succ_apply']
    have hT : (ltmStep I)^[2 * (t + 1)] (liftSeeds I S₀) = ltmStep I (ltmStep I S') := by
      rw [e2, Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [hT, hS1]
    have sumeq : ∀ i, (∑ j ∈ Finset.univ.filter
        (fun j => Sum.inr j ∈ ltmStep I S' ∧ i ∈ I.e j), I.r j i) =
        ∑ j ∈ Finset.univ.filter
          (fun j => i ∈ I.e j ∧ I.θ j - 1 ≤ (S ∩ I.e j).card), I.r j i := by
      intro i
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, o2, taJ]
      tauto
    have q2 : ∀ j, Sum.inr j ∈ ltmStep I (ltmStep I S') ↔ taJ I S j := by
      intro j
      rw [ta_ltm_inr, ta_card_eq I _ S o1, o2]
      unfold taJ; tauto
    refine ⟨?_, ?_, ?_⟩
    · intro i
      rw [ta_ltm_inl, o1, sumeq, ta_step_mem]
    · intro i h
      have h' : I.c i ≤ ∑ j ∈ Finset.univ.filter
          (fun j => Sum.inr j ∈ ltmStep I S' ∧ i ∈ I.e j), I.r j i := by
        have : Finset.univ.filter
            (fun j => Sum.inr j ∈ ltmStep I (ltmStep I S') ∧ i ∈ I.e j) =
            Finset.univ.filter (fun j => Sum.inr j ∈ ltmStep I S' ∧ i ∈ I.e j) := by
          ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, q2, o2]
        rw [this] at h; exact h
      rw [sumeq] at h'
      rw [ta_step_mem]; exact Or.inr h'
    · intro j h
      rw [q2] at h
      unfold taJ at h ⊢
      exact le_trans h (Finset.card_le_card
        (Finset.inter_subset_inter_right (ta_step_ext I S)))

theorem ta_prop1 (I : Instance) (hI : I.Standing)
    (S₀ : Finset (Fin I.n)) :
    (∀ t : ℕ, ∀ i : Fin I.n,
      i ∈ (step I)^[t] S₀ ↔
        Sum.inl i ∈ (ltmStep I)^[2 * t] (liftSeeds I S₀)) ∧
    (∀ i : Fin I.n,
      (∃ t : ℕ, i ∈ (step I)^[t] S₀) ↔
        ∃ t : ℕ, Sum.inl i ∈ (ltmStep I)^[t] (liftSeeds I S₀)) := by
  have key := fun t => ta_invariant I hI.1 S₀ t
  refine ⟨fun t i => ((key t).1 i).symm, fun i => ⟨?_, ?_⟩⟩
  · rintro ⟨t, ht⟩
    exact ⟨2 * t, ((key t).1 i).2 ht⟩
  · rintro ⟨t, ht⟩
    refine ⟨t, ((key t).1 i).1 ?_⟩
    exact ta_iter_ltm_mono I _ (by omega) ht

theorem ta_cor1 (I : Instance) (hI : I.Standing)
    (S₀ : Finset (Fin I.n)) :
    FullyActivates I S₀ ↔
      ∃ t : ℕ, (ltmStep I)^[t] (liftSeeds I S₀) = Finset.univ := by
  have key := fun t => ta_invariant I hI.1 S₀ t
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨2 * t + 1, ?_⟩
    rw [Function.iterate_succ_apply']
    have hf : ∀ i, Sum.inl i ∈ (ltmStep I)^[2 * t] (liftSeeds I S₀) ↔ i ∈ (Finset.univ : Finset (Fin I.n)) := by
      intro i; rw [(key t).1 i, ht]
    ext v
    simp only [Finset.mem_univ, iff_true]
    cases v with
    | inl i => exact ta_ltm_ext I _ ((hf i).2 (Finset.mem_univ _))
    | inr j =>
      rw [ta_ltm_inr, ta_card_eq I _ _ hf]
      right
      rw [Finset.univ_inter]
      have := (hI.2.1 j).2
      omega
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have h2 : (ltmStep I)^[2 * t] (liftSeeds I S₀) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro v
      exact ta_iter_ltm_mono I _ (by omega : t ≤ 2 * t) (by rw [ht]; exact Finset.mem_univ v)
    apply Finset.eq_univ_of_forall
    intro i
    exact ((key t).1 i).1 (by rw [h2]; exact Finset.mem_univ _)

end TraceAdopt.LPReform

open TraceAdopt.LPReform in
theorem solution (I : Instance) (hI : I.Standing)
    (S₀ : Finset (Fin I.n)) :
    FullyActivates I S₀ ↔
      ∃ t : ℕ, (ltmStep I)^[t] (liftSeeds I S₀) = Finset.univ :=
  ta_cor1 I hI S₀

-- Prove2me | solution 1 for ScatCaps.LinearSets.baer_subplane
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:15:57.122996+00:00
-- url     : https://prove2.me/submissions/fdfb759b-db0f-4aec-864d-119ee0336077

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

open ScatCaps.LinearSets in
theorem solution (K : Type*) [Field K] [Fintype K]
    (Fq : Subfield K) (q : ℕ)
    (hq : Nat.card Fq = q) (hK : Fintype.card K = q ^ 2) :
    ∃ U : Set (Fin 3 → K), IsFqSubspace Fq U ∧
      HasRank Fq U 3 ∧ IsScattered Fq (⊤ : Subfield K) U := by
  refine ⟨{v | ∀ i, v i ∈ Fq}, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i
    exact Fq.zero_mem
  · intro u v hu hv i
    exact Fq.add_mem (hu i) (hv i)
  · intro a u hu i
    show (a : K) * u i ∈ Fq
    exact Fq.mul_mem a.2 (hu i)
  · unfold HasRank
    let e : ({v : Fin 3 → K | ∀ i, v i ∈ Fq} : Set (Fin 3 → K)) ≃ (Fin 3 → Fq) :=
      { toFun := fun v i => ⟨v.1 i, v.2 i⟩
        invFun := fun w => ⟨fun i => (w i : K), fun i => (w i).2⟩
        left_inv := fun v => rfl
        right_inv := fun w => rfl }
    rw [Nat.card_congr e, Nat.card_pi]
    simp
  · intro u hu hne c hc
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    have h1 : (c : K) * u i ∈ Fq := by simpa using hc i
    have h2 : (c : K) = ((c : K) * u i) / u i := by field_simp
    rw [h2]
    exact Fq.div_mem h1 (hu i)

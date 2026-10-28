-- Prove2me | solution 1 for ScatCaps.Caps.baer_subplane
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:09:50.449395+00:00
-- url     : https://prove2.me/submissions/99a8cd70-e374-40f8-b45f-2df21e2e191e

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

theorem solution (K : Type*) [Field K] [Fintype K] (Fq : Subfield K) (q : ℕ)
    (hq : Nat.card Fq = q) (hK : Fintype.card K = q ^ 2) :
    ∃ U : Set (Fin 3 → K), ScatCaps.LinearSets.IsFqSubspace Fq U ∧ ScatCaps.LinearSets.HasRank Fq U 3 ∧
      ScatCaps.LinearSets.IsScattered Fq (⊤ : Subfield K) U := by
  refine ⟨{v | ∀ i, v i ∈ Fq}, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i; exact Fq.zero_mem
  · intro u v hu hv i; exact Fq.add_mem (hu i) (hv i)
  · intro a u hu i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Fq.mul_mem a.2 (hu i)
  · unfold ScatCaps.LinearSets.HasRank
    have e : Nat.card {v : Fin 3 → K // ∀ i, v i ∈ Fq} = Nat.card (Fin 3 → Fq) :=
      Nat.card_congr (Equiv.subtypePiEquivPi (p := fun _ (b : K) => b ∈ Fq))
    have e2 : Nat.card ({v | ∀ i, v i ∈ Fq} : Set (Fin 3 → K)) =
        Nat.card {v : Fin 3 → K // ∀ i, v i ∈ Fq} := rfl
    rw [e2, e, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
  · intro u hu hne c hc
    have : ∃ i, u i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    obtain ⟨i, hi⟩ := this
    have h1 : (c : K) * u i ∈ Fq := by
      have := hc i
      simpa only [Pi.smul_apply, smul_eq_mul] using this
    rw [← mul_inv_cancel_right₀ hi (c : K)]
    exact Fq.mul_mem h1 (Fq.inv_mem (hu i))

-- Prove2me | solution 1 for SpinStatistics.composite_exchange_sign
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T11:20:56.206693+00:00
-- url     : https://prove2.me/submissions/c67aa9b5-4720-493c-8991-26b596064f50

import Mathlib
import Definitions.Def_SpinStatistics_Defs

set_option autoImplicit false

/-- Swap the composite label of exactly the constituent slots lying in `S`. -/
def swapSlots_18014d61 {k : ℕ} (S : Finset (Fin k)) (p : Fin 2 × Fin k) : Fin 2 × Fin k :=
  if p.2 ∈ S then (Equiv.swap (0 : Fin 2) 1 p.1, p.2) else p

open SpinStatistics in
theorem swapSlots_insert_18014d61 {k : ℕ} (S : Finset (Fin k)) (i : Fin k) (hi : i ∉ S) :
    swapSlots_18014d61 (insert i S) = swapSlots_18014d61 S ∘ swapConstituent i := by
  funext p
  obtain ⟨a, j⟩ := p
  by_cases hj : j = i
  · subst hj
    simp [swapSlots_18014d61, swapConstituent, hi]
  · simp [swapSlots_18014d61, swapConstituent, hj]

open SpinStatistics in
theorem solution {X : Type*} {k : ℕ} (fermion : Fin k → Prop)
    [DecidablePred fermion] (Ψ : (Fin 2 × Fin k → X) → ℂ)
    (hexch : ∀ i c, Ψ (c ∘ swapConstituent i) = (if fermion i then -1 else 1) * Ψ c) :
    ∀ c, Ψ (c ∘ swapComposites) =
      (-1) ^ (Finset.univ.filter fermion).card * Ψ c := by
  have key : ∀ S : Finset (Fin k), ∀ c : Fin 2 × Fin k → X,
      Ψ (c ∘ swapSlots_18014d61 S) = (-1) ^ (S.filter fermion).card * Ψ c := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro c
      have h0 : swapSlots_18014d61 (∅ : Finset (Fin k)) = id := by
        funext p; simp [swapSlots_18014d61]
      simp [h0]
    | @insert i S hi ih =>
      intro c
      rw [swapSlots_insert_18014d61 S i hi, ← Function.comp_assoc, hexch, ih,
        Finset.filter_insert]
      by_cases hf : fermion i
      · have hni : i ∉ S.filter fermion := fun h => hi (Finset.mem_filter.mp h).1
        rw [if_pos hf, if_pos hf, Finset.card_insert_of_notMem hni, pow_succ]
        ring
      · rw [if_neg hf, if_neg hf]
        ring
  intro c
  have hu : swapSlots_18014d61 (Finset.univ : Finset (Fin k)) = swapComposites := by
    funext p; simp [swapSlots_18014d61, swapComposites]
  rw [← hu]
  exact key Finset.univ c

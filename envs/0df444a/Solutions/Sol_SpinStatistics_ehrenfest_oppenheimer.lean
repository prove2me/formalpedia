-- Prove2me | solution 1 for SpinStatistics.ehrenfest_oppenheimer
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:50:18.77398+00:00
-- url     : https://prove2.me/submissions/16e4a100-c796-40b4-b935-dca30960c348

import Mathlib
import Definitions.Def_SpinStatistics_Defs

set_option autoImplicit false

/-- Swap the composite label of exactly the constituent slots lying in `S`. -/
def swapSlots_f20e4bc1 {k : ℕ} (S : Finset (Fin k)) (p : Fin 2 × Fin k) : Fin 2 × Fin k :=
  if p.2 ∈ S then (Equiv.swap (0 : Fin 2) 1 p.1, p.2) else p

open SpinStatistics in
theorem swapSlots_insert_f20e4bc1 {k : ℕ} (S : Finset (Fin k)) (i : Fin k) (hi : i ∉ S) :
    swapSlots_f20e4bc1 (insert i S) = swapSlots_f20e4bc1 S ∘ swapConstituent i := by
  funext p
  obtain ⟨a, j⟩ := p
  by_cases hj : j = i
  · subst hj
    simp [swapSlots_f20e4bc1, swapConstituent, hi]
  · simp [swapSlots_f20e4bc1, swapConstituent, hj]

open SpinStatistics in
/-- Clebsch–Gordan coupling preserves the parity of the sum of doubled spins. -/
theorem canAddTo_parity_f20e4bc1 (l : List ℕ) (J : ℕ) (h : CanAddTo l J) :
    J % 2 = l.sum % 2 := by
  induction h with
  | nil => simp
  | @cons a b J l _ _ _ _ hpar ih =>
    rw [List.sum_cons]
    omega

open SpinStatistics in
theorem solution {X : Type*} {k : ℕ} (s : Fin k → ℕ)
    (Ψ : (Fin 2 × Fin k → X) → ℂ)
    (hexch : ∀ i c, Ψ (c ∘ swapConstituent i) = (-1) ^ s i * Ψ c)
    (J : ℕ) (hJ : CanAddTo (List.ofFn s) J) :
    ∀ c, Ψ (c ∘ swapComposites) = (-1) ^ J * Ψ c := by
  have key : ∀ S : Finset (Fin k), ∀ c : Fin 2 × Fin k → X,
      Ψ (c ∘ swapSlots_f20e4bc1 S) = (-1) ^ (∑ i ∈ S, s i) * Ψ c := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro c
      have h0 : swapSlots_f20e4bc1 (∅ : Finset (Fin k)) = id := by
        funext p; simp [swapSlots_f20e4bc1]
      simp [h0]
    | @insert i S hi ih =>
      intro c
      rw [swapSlots_insert_f20e4bc1 S i hi, ← Function.comp_assoc, hexch, ih,
        Finset.sum_insert hi, pow_add]
      ring
  intro c
  have hu : swapSlots_f20e4bc1 (Finset.univ : Finset (Fin k)) = swapComposites := by
    funext p; simp [swapSlots_f20e4bc1, swapComposites]
  rw [← hu, key Finset.univ c]
  have hpar := canAddTo_parity_f20e4bc1 _ _ hJ
  rw [List.sum_ofFn] at hpar
  rw [neg_one_pow_eq_pow_mod_two (R := ℂ), ← hpar, ← neg_one_pow_eq_pow_mod_two]

-- Prove2me | solution 1 for QuantumMaxCutEnergy.internalSum_le_half_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T05:33:42.432756+00:00
-- url     : https://prove2.me/submissions/a31e73e2-77bb-43c5-ba81-9b9f879413c6

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Mathlib
import Theorems.Thm_QuantumMaxCutEnergy_two_mul_internalSum_le_sum_load

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

/-- A vertex set whose loads are at most `1` carries internal edge mass at most half its size. -/
theorem solution {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v, loadAt x v ≤ 1) (S : Finset (Fin n)) :
    internalSum x S ≤ ((S.card : ℝ)) / 2 := by
  have h1 := two_mul_internalSum_le_sum_load x hx S
  have h2 : ∑ v ∈ S, loadAt x v ≤ (S.card : ℝ) := by
    have h3 : ∑ v ∈ S, loadAt x v ≤ ∑ v ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hload v)
    simpa [Finset.sum_const, nsmul_eq_mul] using h3
  linarith

#print axioms solution

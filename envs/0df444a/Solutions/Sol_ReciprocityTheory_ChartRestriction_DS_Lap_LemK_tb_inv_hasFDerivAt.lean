-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.tb_inv_hasFDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:01.775546+00:00
-- url     : https://prove2.me/submissions/df930a7c-67db-4d40-93d5-8337bd3af2e6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution {x : Matrix (Fin n) (Fin n) ℂ} (hx : IsUnit x) :
    ∃ L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ,
      HasFDerivAt (fun z : Matrix (Fin n) (Fin n) ℂ => z⁻¹) L x ∧ ∀ h, L h = -(x⁻¹ * h * x⁻¹) := by
  refine ⟨-(ContinuousLinearMap.mulLeftRight ℂ (Matrix (Fin n) (Fin n) ℂ) (↑hx.unit⁻¹) (↑hx.unit⁻¹)),
    ?_, ?_⟩
  · have h := hasFDerivAt_ringInverse (𝕜 := ℂ) hx.unit
    rw [hx.unit_spec] at h
    have e : (fun z : Matrix (Fin n) (Fin n) ℂ => z⁻¹) = Ring.inverse :=
      funext Matrix.nonsing_inv_eq_ringInverse
    rw [e]
    exact h
  · intro h
    simp only [Matrix.coe_units_inv, hx.unit_spec]
    exact congrArg Neg.neg (ContinuousLinearMap.mulLeftRight_apply ℂ (Matrix (Fin n) (Fin n) ℂ) x⁻¹ x⁻¹ h)
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK

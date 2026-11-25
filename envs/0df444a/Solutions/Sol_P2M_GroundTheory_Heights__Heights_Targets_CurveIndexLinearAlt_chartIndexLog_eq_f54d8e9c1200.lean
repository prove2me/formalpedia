-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_chartIndexLog_eq_f54d8e9c1200
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:21.488904+00:00
-- url     : https://prove2.me/submissions/2ba85b34-83e1-464a-86f6-7d00f2ea6dc4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveIndexLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveIndexLinear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_chartUnit_one_b5fc04b87582
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_ne_zero_a60dcb0d33ce

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
theorem _root_.solution {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a : K → ℤ) :
    chartIndexLog y c a 1 = Real.log (genIndex (secIdeal y c a) (curveRing y).toAddSubgroup) := by
  have hu := cu_ne_zero hc a
  have hinj : Function.Injective (AddMonoidHom.mulLeft (cu y c a)⁻¹) := fun x x' h =>
    mul_right_injective₀ (inv_ne_zero hu) h
  have hB : (curveRing y).toAddSubgroup =
      (curveMul y (cu y c a)).map (AddMonoidHom.mulLeft (cu y c a)⁻¹) := by
    rw [curveMul, AddSubgroup.map_map]
    have e : (AddMonoidHom.mulLeft (cu y c a)⁻¹).comp (AddMonoidHom.mulLeft (cu y c a)) = AddMonoidHom.id Ω := by
      ext x
      simp [hu]
    rw [e, AddSubgroup.map_id]
  rw [chartIndexLog, chartUnit_one, hB, secIdeal, genIndex, genIndex,
    AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
end GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_cu_add_5d540c60428b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:20:33.44589+00:00
-- url     : https://prove2.me/submissions/e23d5694-c6fc-4f05-bc49-eceaa6b53bb4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveIndexLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveIndexLinear

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
theorem _root_.solution {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a a' : K → ℤ) :
    cu y c (a + a') = cu y c a * cu y c a' := by
  rw [cu, cu, cu, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => zpow_add₀ (hc k) _ _
end GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_zpow_mem_of_9a48d073fbd3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:20:39.661005+00:00
-- url     : https://prove2.me/submissions/ec1ac7b5-bf9e-499b-9815-4a199ac1158f

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
theorem _root_.solution {S : Subring Ω} {x : Ω} (hx : x ∈ S) (hx' : x⁻¹ ∈ S) (n : ℤ) : x ^ n ∈ S := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact S.pow_mem hx n
  | negSucc n => rw [zpow_negSucc, ← inv_pow]; exact S.pow_mem hx' _
end GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt

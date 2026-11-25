-- Prove2me | solution 1 for P2M_GlobalTheory_DiscEval_coeffPoly_bind__ea251764de75
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:35:35.31112+00:00
-- url     : https://prove2.me/submissions/04f13731-4a86-4a58-b433-343c6a90fab1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_DiscEval_coeffPoly_sum
import Theorems.Thm_GlobalTheory_DiscEval_coeffPoly_C_mul_map
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X



set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
open MvPolynomial
variable {K : Type*} [Field K] {σ τ : Type*}
namespace GlobalTheory.DiscEval
theorem _root_.solution (m : ℤ) (g : σ → MvPolynomial τ K) (G : MvPolynomial σ K⸨X⸩) :
    coeffPoly m (bind₁ (fun k => map (HahnSeries.C : K →+* K⸨X⸩) (g k)) G) =
      bind₁ g (coeffPoly m G) := by
  conv_lhs => rw [G.as_sum]
  rw [map_sum, coeffPoly_sum, coeffPoly, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [bind₁_monomial, bind₁_monomial, ← coeffPoly_C_mul_map, map_prod]
  simp only [map_pow]
end GlobalTheory.DiscEval

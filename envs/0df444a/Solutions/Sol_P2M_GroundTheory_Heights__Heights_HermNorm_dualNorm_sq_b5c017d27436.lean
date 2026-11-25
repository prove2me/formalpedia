-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_sq_b5c017d27436
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:54:43.190794+00:00
-- url     : https://prove2.me/submissions/bdbcd687-282b-4cd9-b148-761d4d142d3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutOffLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace HermNorm
theorem _root_.solution (h : HermNorm n) (y : Fin n → ℂ) :
    h.dualNorm y ^ 2 = ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2 :=
  Real.sq_sqrt (by positivity)
end HermNorm
end GroundTheory.Heights₂.Heights

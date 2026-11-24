-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_pointOf_eq_zero_1a71672ffe50
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:39.542606+00:00
-- url     : https://prove2.me/submissions/82094c60-51fc-4215-a5cd-b615f1d37d69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine

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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace HermNorm
theorem _root_.solution (h : HermNorm n) {y : EuclideanSpace ℂ (Fin n)}
    (hy : h.pointOf y = 0) : y = 0 := by
  have hu : IsUnit h.matᵀ := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_transpose]; exact h.isUnit_det)
  have hv : (fun i => y i) = 0 :=
    Matrix.mulVec_injective_iff_isUnit.mpr hu (by simpa [HermNorm.pointOf] using hy)
  ext i
  simpa using congrFun hv i
end HermNorm
end GroundTheory.Heights₂.Heights

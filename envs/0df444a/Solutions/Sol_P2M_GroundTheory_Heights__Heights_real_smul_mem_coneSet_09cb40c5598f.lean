-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_real_smul_mem_coneSet_09cb40c5598f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:39:31.330983+00:00
-- url     : https://prove2.me/submissions/f7534061-32b4-444b-b017-b0115002475c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFibreAverage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_smul_mem_zeroSet_ab37cf5939d2


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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hJ : IsProjPrime J) {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ coneSet h J) (t : ℝ) :
    t • y ∈ coneSet h J := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  intro q hq
  rw [HermNorm.pointOf_smul']
  exact PointLine.smul_mem_zeroSet hJ.isHomog hy (t : ℂ) q hq
end GroundTheory.Heights₂.Heights

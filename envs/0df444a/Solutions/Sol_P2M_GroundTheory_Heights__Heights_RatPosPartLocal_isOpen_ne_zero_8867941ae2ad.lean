-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatPosPartLocal_isOpen_ne_zero_8867941ae2ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:48:01.237625+00:00
-- url     : https://prove2.me/submissions/54487752-82ce-4cbb-9a04-5925346576eb

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatPosPartLocal

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
noncomputable section
open GroundTheory.Heights₂.Heights.RatPosPartLocal
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.RatPosPartLocal
theorem _root_.solution (q : MvPolynomial (Fin n) ℂ) : IsOpen {x : Fin n → ℂ | eval x q ≠ 0} :=
  isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const
end GroundTheory.Heights₂.Heights.RatPosPartLocal

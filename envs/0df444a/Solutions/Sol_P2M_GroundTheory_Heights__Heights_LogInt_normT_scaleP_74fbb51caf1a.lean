-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_normT_scaleP_74fbb51caf1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:40:08.23906+00:00
-- url     : https://prove2.me/submissions/8d7cfc77-dc01-42f1-a699-21b059a79156

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_smul_549dac818b96
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_scale_inGroup_apply_same_c953392429ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_scale_inGroup_apply_of_ne_6de922e60143

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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (h : HermNorm n) (T : Finset (Fin k)) (i : Fin k) (θ : ℝ)
    (u : Fin k × Fin n → ℂ) :
    normT h T (scaleP (inGroup i) (circleMap 0 1 θ) u) =
      scaleP (inGroup i) (circleMap 0 1 θ) (normT h T u) := by
  funext ⟨a, b⟩
  by_cases hi : a = i
  · subst hi
    simp only [normT, h.li_norm_smul, norm_circleMap_zero, abs_one, one_mul, scale_inGroup_apply_same]
    split_ifs <;> ring
  ·     simp only [normT, scale_inGroup_apply_of_ne i a hi]
end GroundTheory.Heights₂.Heights.LogInt

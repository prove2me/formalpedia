-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_hermNorm_490b6c9ab1d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:45:27.862089+00:00
-- url     : https://prove2.me/submissions/585f5871-ce88-4c5e-bcd8-ff79b1e1882c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_norm_fe0404d8d94b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_exists_eq_ofPointMatrix_f9a576162836
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_formNorm_9c335fffca42

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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
variable {k : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsHeight
theorem _root_.solution (h : HermNorm n) : Continuous h.norm := by
  obtain ⟨S, hS, rfl⟩ := exists_eq_ofPointMatrix h
  rw [show (ofPointMatrix S hS).norm = IndefiniteRowSideFullHecke.ArithBezout.formNorm S from
    funext (ofPointMatrix_norm S hS)]
  exact continuous_formNorm S
end GroundTheory.Heights₂.Heights.ObjectsHeight

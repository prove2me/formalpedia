-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_finGaussLog_eq_6c42ce4ca209
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:44:59.353103+00:00
-- url     : https://prove2.me/submissions/3e4cf794-a027-4af4-8b30-74704e225462

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_finsum_log_gaussNorm_2b096fa7246f

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
theorem _root_.solution {ι : Type*} (f : MvPolynomial ι ℚ) :
    IndefiniteRowSideFullHecke.ArithBezout.finGaussLog f =
      ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), Real.log (gaussNorm v f) :=
  (finsum_log_gaussNorm f).symm
end GroundTheory.Heights₂.Heights.ObjectsHeight

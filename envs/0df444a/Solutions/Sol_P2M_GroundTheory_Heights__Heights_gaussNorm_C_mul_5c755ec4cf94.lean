-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_gaussNorm_C_mul_5c755ec4cf94
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:48.049695+00:00
-- url     : https://prove2.me/submissions/b44ae148-8902-46a6-81fb-5f8ebac8868b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_mul_e42d0b485d41
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_C_3de71e041495

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
open MvPolynomial NumberField
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (c : K)
    (f : MvPolynomial ι K) :
    gaussNorm v (C c * f) = NumberField.HeightOneSpectrum.adicAbv K v c * gaussNorm v f := by
  rw [gaussNorm_mul, gaussNorm_C]
end GroundTheory.Heights₂.Heights

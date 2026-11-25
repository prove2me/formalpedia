-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_gaussNorm_mul_e42d0b485d41
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:47.941007+00:00
-- url     : https://prove2.me/submissions/52ab6882-04fa-4d0f-b249-b8bd9427fcdd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_mul_ff1ac2fe2a0f

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
theorem _root_.solution (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    (f g : MvPolynomial ι K) : gaussNorm v (f * g) = gaussNorm v f * gaussNorm v g :=
  gaussNormOf_mul (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v) f g
end GroundTheory.Heights₂.Heights

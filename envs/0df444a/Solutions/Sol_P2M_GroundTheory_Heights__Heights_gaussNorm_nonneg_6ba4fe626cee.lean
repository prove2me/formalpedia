-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_gaussNorm_nonneg_6ba4fe626cee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:35:51.624519+00:00
-- url     : https://prove2.me/submissions/474abbd7-103a-4eec-8a4e-16a48069522c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_nonneg_e5b131e01688

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
    (f : MvPolynomial ι K) : 0 ≤ gaussNorm v f := gaussNormOf_nonneg _ f
end GroundTheory.Heights₂.Heights

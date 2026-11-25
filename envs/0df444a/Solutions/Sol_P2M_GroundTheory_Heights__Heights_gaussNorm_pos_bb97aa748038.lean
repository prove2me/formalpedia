-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_gaussNorm_pos_bb97aa748038
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:35:55.94431+00:00
-- url     : https://prove2.me/submissions/ac21ac9c-8aa8-4537-8cd3-43ef58da2d04

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_pos_f7b56068fd3a

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
    {f : MvPolynomial ι K} (hf : f ≠ 0) : 0 < gaussNorm v f := gaussNormOf_pos _ hf
end GroundTheory.Heights₂.Heights

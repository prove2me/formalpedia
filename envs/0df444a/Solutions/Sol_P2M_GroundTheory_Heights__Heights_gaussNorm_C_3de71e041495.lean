-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_gaussNorm_C_3de71e041495
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:55.857799+00:00
-- url     : https://prove2.me/submissions/4941f015-2ec0-4dbb-8662-630605b97b78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_C_6e81e4d023f3

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
theorem _root_.solution (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (c : K) :
    gaussNorm v (C c : MvPolynomial ι K) = NumberField.HeightOneSpectrum.adicAbv K v c :=
  gaussNormOf_C _ c
end GroundTheory.Heights₂.Heights

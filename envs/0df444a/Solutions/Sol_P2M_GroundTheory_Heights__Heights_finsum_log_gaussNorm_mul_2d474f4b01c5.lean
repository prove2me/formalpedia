-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finsum_log_gaussNorm_mul_2d474f4b01c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:57:11.558564+00:00
-- url     : https://prove2.me/submissions/8453ee68-4272-4fc7-8f8b-ed920d5e88b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_mul_e42d0b485d41
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_pos_bb97aa748038
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_log_gaussNorm_support_finite_3084f6843453


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
theorem _root_.solution {ι : Type*} {f g : MvPolynomial ι K} (hf : f ≠ 0) (hg : g ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (f * g)) =
      (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f)) +
        ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v g) := by
  rw [← finsum_add_distrib (log_gaussNorm_support_finite hf) (log_gaussNorm_support_finite hg)]
  refine finsum_congr fun v => ?_
  rw [gaussNorm_mul, Real.log_mul (gaussNorm_pos v hf).ne' (gaussNorm_pos v hg).ne']
end GroundTheory.Heights₂.Heights

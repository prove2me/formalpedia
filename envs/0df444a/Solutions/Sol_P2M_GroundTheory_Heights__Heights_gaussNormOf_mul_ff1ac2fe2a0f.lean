-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_gaussNormOf_mul_ff1ac2fe2a0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:43:11.708117+00:00
-- url     : https://prove2.me/submissions/ec1a2615-80ac-45b4-8352-1dad1bdd94ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_zero_a7c5c5873dc3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_mul_le_e992443b279f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_gaussNormOf_mul_a9f651f2e985

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
variable {R : Type*} [CommRing R] {ι : Type*} (w : AbsoluteValue R ℝ)
variable {w}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (hna : IsNonarchimedean w) (f g : MvPolynomial ι R) :
    gaussNormOf w (f * g) = gaussNormOf w f * gaussNormOf w g := by
  by_cases hf : f = 0
  · simp [hf, gaussNormOf_zero]
  by_cases hg : g = 0
  · simp [hg, gaussNormOf_zero]
  exact le_antisymm (gaussNormOf_mul_le hna f g) (le_gaussNormOf_mul hna hf hg)
end GroundTheory.Heights₂.Heights

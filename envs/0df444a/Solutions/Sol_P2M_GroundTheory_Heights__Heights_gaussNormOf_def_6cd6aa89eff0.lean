-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_gaussNormOf_def_6cd6aa89eff0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:38:08.716539+00:00
-- url     : https://prove2.me/submissions/1b45503d-613a-4bd4-8cf4-700e11808a22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite

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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (f : MvPolynomial ι R) :
    gaussNormOf w f = (((f.support.sup fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal)) : NNReal) : ℝ) :=
  rfl
end GroundTheory.Heights₂.Heights

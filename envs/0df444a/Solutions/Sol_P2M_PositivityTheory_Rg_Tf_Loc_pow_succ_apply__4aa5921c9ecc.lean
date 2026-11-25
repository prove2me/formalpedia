-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Tf_Loc_pow_succ_apply__4aa5921c9ecc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:51:14.923094+00:00
-- url     : https://prove2.me/submissions/3c6df661-de08-4424-8558-96c51a402d98

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Polynomial
open scoped ENNReal
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Tf PositivityTheory.Rg.Tf.Loc
noncomputable section
variable {G : Type*} [Group G]
namespace PositivityTheory.Rg.Tf.Loc
theorem _root_.solution (θ : Monoid.End G) (m : ℕ) (g : G) :
    (θ ^ (m + 1)) g = θ ((θ ^ m) g) := by
  rw [pow_succ']; rfl
end PositivityTheory.Rg.Tf.Loc

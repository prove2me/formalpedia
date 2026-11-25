-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.pow_succ_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:54:13.199881+00:00
-- url     : https://prove2.me/submissions/9619642f-9022-458a-963f-65a312c24441

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
    (θ ^ (m + 1)) g = (θ ^ m) (θ g) := by
  rw [pow_succ]; rfl
end PositivityTheory.Rg.Tf.Loc

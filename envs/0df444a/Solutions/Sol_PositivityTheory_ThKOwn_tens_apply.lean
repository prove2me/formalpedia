-- Prove2me | solution 1 for PositivityTheory.ThKOwn.tens_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:31.937742+00:00
-- url     : https://prove2.me/submissions/b9bd68a4-fec9-43c4-ad84-52f42aef8c1b

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_NormIterComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKOwn
open scoped SchwartzMap ContDiff
variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
namespace PositivityTheory.ThKOwn
theorem _root_.solution (φ : 𝓢(A, ℂ)) (f : 𝓢(B, ℂ)) (a : A) (b : B) : tens φ f (WithLp.toLp 2 (a, b)) = φ a * f b := rfl
end PositivityTheory.ThKOwn

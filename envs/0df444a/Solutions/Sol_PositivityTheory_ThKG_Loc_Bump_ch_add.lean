-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.ch_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:02:14.563925+00:00
-- url     : https://prove2.me/submissions/20cdeea2-d6d7-4a11-b6a0-0973ba9bcd3c

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped FourierTransform SchwartzMap RealInnerProductSpace
variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (s t : ℝ) : ch (s + t) = ch s * ch t := by
  rw [ch, ch, ch, ← Complex.exp_add]; congr 1; push_cast; ring
end PositivityTheory.ThKG.Loc.Bump

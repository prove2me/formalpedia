-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.norm_ch
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:49.965906+00:00
-- url     : https://prove2.me/submissions/c12ca2ef-0902-4b2e-94af-4309ea522704

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
theorem _root_.solution (t : ℝ) : ‖ch t‖ = 1 := by
  have : (2 * Real.pi * Complex.I * t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [ch, this, Complex.norm_exp_ofReal_mul_I]
end PositivityTheory.ThKG.Loc.Bump

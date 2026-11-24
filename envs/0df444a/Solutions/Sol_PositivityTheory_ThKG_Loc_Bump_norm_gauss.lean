-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.norm_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:32.958796+00:00
-- url     : https://prove2.me/submissions/856960ae-31eb-4e45-afc9-cf0278afe467

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian

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
open scoped ComplexConjugate
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (z : ℂ) : ‖Complex.exp (-2 * Real.pi * (‖z‖ : ℂ) ^ 2)‖ = Real.exp (-2 * Real.pi * ‖z‖ ^ 2) := by
  have : (-2 * Real.pi * (‖z‖ : ℂ) ^ 2 : ℂ) = ((-2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal]
end PositivityTheory.ThKG.Loc.Bump

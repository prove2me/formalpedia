-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.FT_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:09:45.678254+00:00
-- url     : https://prove2.me/submissions/e4903a40-1dc5-42ff-b34b-f011c1b2b7bc

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_pr_add
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_ch_add


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
open scoped SchwartzMap RealInnerProductSpace
variable {ι : Type} [Fintype ι] {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X] {K : Type} [TopologicalSpace K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (g : (ι → ℂ) → ℂ) (b t : ι → ℂ) : ∫ x, ch (-pr x t) * g (x + b) = ch (pr b t) * FT g t := by
  rw [FT, ← integral_const_mul, ← integral_add_right_eq_self (fun x => ch (pr b t) * (ch (-pr x t) * g x)) b]
  congr 1; funext x
  rw [← mul_assoc, ← ch_add, pr_add]; congr 2; ring
end PositivityTheory.ThKG.Loc.Bump

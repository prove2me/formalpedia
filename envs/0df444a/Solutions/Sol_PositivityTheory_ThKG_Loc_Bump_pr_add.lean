-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.pr_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:03:17.670776+00:00
-- url     : https://prove2.me/submissions/6ef628ab-31fc-4fee-9823-b4b7d2ed91bf

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap RealInnerProductSpace
variable {ι : Type} [Fintype ι] {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X] {K : Type} [TopologicalSpace K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (x y t : ι → ℂ) : pr (x + y) t = pr x t + pr y t := by
  simp [pr, add_mul, Finset.sum_add_distrib, mul_add]
end PositivityTheory.ThKG.Loc.Bump

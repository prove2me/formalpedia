-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.cont_bet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:22:35.586789+00:00
-- url     : https://prove2.me/submissions/6c990f2d-8e82-4fb7-a693-ff67f41ea826

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_RationalWeightSuccMulInvNorm

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
open scoped SchwartzMap RealInnerProductSpace ComplexConjugate
variable {ι : Type} [Fintype ι] {n : Type} [Fintype n] {K : Type} [TopologicalSpace K]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution {ξ : K → ι → n → ℂ} (h : Continuous ξ) : Continuous (bet ξ) := by unfold bet; fun_prop
end PositivityTheory.ThKG.Loc.Bump

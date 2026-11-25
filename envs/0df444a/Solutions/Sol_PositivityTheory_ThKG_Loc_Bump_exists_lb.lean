-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.exists_lb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:06.703077+00:00
-- url     : https://prove2.me/submissions/24605439-4835-4382-8b9d-b9e6f6ac4f3e

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
theorem _root_.solution {α : Type} [TopologicalSpace α] [CompactSpace α] {g : α → ι → ℝ} (h : ∀ w, Continuous fun a => g a w)
    (hp : ∀ a w, 0 < g a w) : ∃ m : ℝ, 0 < m ∧ ∀ a w, m ≤ g a w := by
  letI : TopologicalSpace ι := ⊥
  haveI : DiscreteTopology ι := ⟨rfl⟩
  have hc : Continuous fun q : α × ι => g q.1 q.2 := continuous_prod_of_discrete_right.2 h
  obtain ⟨m, hm, hb⟩ := isCompact_univ.exists_forall_le' hc.continuousOn (a := 0) fun q _ => hp q.1 q.2
  exact ⟨m, hm, fun a w => hb (a, w) trivial⟩
end PositivityTheory.ThKG.Loc.Bump

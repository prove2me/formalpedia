-- Prove2me | solution 1 for P2M_PositivityTheory_ThKG_Loc_Bump_norming__019b125911dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:49:51.882807+00:00
-- url     : https://prove2.me/submissions/8fc4040a-a166-43bd-a56e-b7c0ef13fbdd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_SliceAn
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_norming

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
open scoped SchwartzMap NNReal
variable {S : Type} [AddCommGroup S] [Module ℂ S]
variable [TopologicalSpace S] [IsTopologicalAddGroup S]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (q : Seminorm ℂ S) (hq : Continuous q) (g : S) : ∃ T : S →L[ℂ] ℂ, ‖T g‖ = q g ∧ ∀ x, ‖T x‖ ≤ q x := by
  obtain ⟨T, h1, h2⟩ := norming q g
  exact ⟨toCLM q hq T 1 (by simpa using h2), h1, h2⟩
end PositivityTheory.ThKG.Loc.Bump

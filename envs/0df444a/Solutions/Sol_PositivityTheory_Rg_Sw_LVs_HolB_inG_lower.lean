-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.HolB.inG_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:47:09.684628+00:00
-- url     : https://prove2.me/submissions/b4e596d3-5018-4f8e-b7ae-b1861c4d9e58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_HermRealSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology Set Metric Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.HolB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.HolB
theorem _root_.solution {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) : InG (fromBlocks 1 0 c 1 : M2 n) := by
  unfold InG JJ
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, hc]
end PositivityTheory.Rg.Sw.LVs.HolB

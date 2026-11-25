-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.dp_card_blkB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:54.728987+00:00
-- url     : https://prove2.me/submissions/cc6f3b37-b082-4646-a131-7342aea33b74

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_dp_card_blkA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {j : ℕ} (hj : j ≤ n) : Fintype.card (blkB (n := n) j) = n - j := by
  rw [Fintype.card_coe, blkB, Finset.card_compl, Fintype.card_fin, ← Fintype.card_coe, dp_card_blkA hj]
end PositivityTheory.Rg.Sw.LVs

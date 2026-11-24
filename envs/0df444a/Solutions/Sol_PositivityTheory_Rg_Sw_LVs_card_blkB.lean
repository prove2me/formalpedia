-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.card_blkB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:08.005464+00:00
-- url     : https://prove2.me/submissions/4a8c0cfe-0f57-4a8c-bc64-def0ddf51b5c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_card_blkA

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {j : ℕ} (hj : j ≤ n) : Fintype.card (blkB (n := n) j) = n - j := by
  rw [Fintype.card_coe, blkB, Finset.card_compl, Fintype.card_fin, ← Fintype.card_coe, card_blkA hj]
end PositivityTheory.Rg.Sw.LVs

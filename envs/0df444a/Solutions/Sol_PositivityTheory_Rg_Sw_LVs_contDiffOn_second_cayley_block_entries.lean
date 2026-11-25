-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.contDiffOn_second_cayley_block_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:56:03.613108+00:00
-- url     : https://prove2.me/submissions/4533eb61-a92b-47d1-8dc4-5f25cdc97d16

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_matrix
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_contDiff_second_cayley_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (s : Set (M2 n)) : ∀ i j, ContDiffOn ℂ ∞ (fun x => u2 x i j) s := fun i j =>
  ((cdo_matrix (M := u2 (n := n)) (s := s)).1 contDiff_second_cayley_block.contDiffOn) i j
end PositivityTheory.Rg.Sw.LVs

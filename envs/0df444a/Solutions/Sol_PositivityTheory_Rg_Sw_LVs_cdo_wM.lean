-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.cdo_wM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:04.098891+00:00
-- url     : https://prove2.me/submissions/ff458045-3df6-40e1-b5f8-0500450a02de

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_inv
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_contDiffOn_first_cayley_block_entries
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_contDiffOn_second_cayley_block_entries

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
theorem _root_.solution (s : Set (M2 n)) (hs : ∀ x ∈ s, (u2 x).det ≠ 0) : ∀ i j, ContDiffOn ℂ ∞ (fun x => wM x i j) s :=
  cdo_mul (cdo_inv (contDiffOn_second_cayley_block_entries s) hs) (contDiffOn_first_cayley_block_entries s)
end PositivityTheory.Rg.Sw.LVs

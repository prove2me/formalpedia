-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.contDiffOn_scalar_section_of_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:07.837812+00:00
-- url     : https://prove2.me/submissions/286e200b-6358-426f-a5d0-7a567f971b2d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_det
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_zpow
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
theorem _root_.solution (p q : ℤ) : ContDiffOn ℂ ∞ (f0 (n := n) p q) {x | (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0} := by
  unfold f0
  exact (cdo_zpow (cdo_det (contDiffOn_first_cayley_block_entries _)) (fun x hx => hx.1) _).mul (cdo_zpow (cdo_det (contDiffOn_second_cayley_block_entries _)) (fun x hx => hx.2) _)
end PositivityTheory.Rg.Sw.LVs

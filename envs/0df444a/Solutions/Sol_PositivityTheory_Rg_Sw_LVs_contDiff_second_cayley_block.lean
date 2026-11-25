-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.contDiff_second_cayley_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:24.142712+00:00
-- url     : https://prove2.me/submissions/16f8621d-c2c5-40e4-9499-1a305ea29e59

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_matrix
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cd_entry

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
theorem _root_.solution : ContDiff ℂ ∞ (u2 (n := n)) := by
  rw [contDiff_iff_contDiffAt]; intro x
  refine (cdo_matrix (s := Set.univ)).2 (fun i j => ?_) |>.contDiffAt Filter.univ_mem
  simp only [u2, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
    Matrix.of_apply, smul_eq_mul]
  exact ((contDiff_const.mul (cd_entry _ _)).neg.add (cd_entry _ _)).contDiffOn
end PositivityTheory.Rg.Sw.LVs

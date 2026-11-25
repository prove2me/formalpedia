-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.isOpen_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:20:08.235124+00:00
-- url     : https://prove2.me/submissions/a4d5850b-9ab0-4fb1-b7d7-c3dc0473c186

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_continuous_first_cayley_block_map
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_continuous_second_cayley_block_map
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_continuousOn_inverse_first_block

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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution : IsOpen (Dom n) := by
  have hdet : Continuous (fun x : M2 n => x.det) := continuous_id.matrix_det
  have h0 : IsOpen {x : M2 n | x.det ≠ 0} := isOpen_ne_fun hdet continuous_const
  have e : Dom n = ({x : M2 n | x.det ≠ 0} ∩ (fun x => ub1 x) ⁻¹' {M | M.det ≠ 0}) ∩
      ({x | (u1 x).det ≠ 0} ∩ {x | (u2 x).det ≠ 0}) := by
    ext x
    simp only [Dom, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, isUnit_iff_ne_zero]
    tauto
  rw [e]
  refine IsOpen.inter (continuousOn_inverse_first_block.isOpen_inter_preimage h0
    (isOpen_ne_fun continuous_id.matrix_det continuous_const)) (IsOpen.inter ?_ ?_)
  · exact isOpen_ne_fun continuous_first_cayley_block_map.matrix_det continuous_const
  · exact isOpen_ne_fun continuous_second_cayley_block_map.matrix_det continuous_const
end PositivityTheory.Rg.Sw.LVs

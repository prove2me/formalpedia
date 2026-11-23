-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.continuous_second_cayley_block_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:53:49.413725+00:00
-- url     : https://prove2.me/submissions/7dead605-d7e9-4cde-b155-fae09121027f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____fb38dccd8d2c
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____c307b9145f64

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
theorem _root_.solution : Continuous (fun x : M2 n => u2 x) := by
  show Continuous (fun x : M2 n => -(Complex.I • x.toBlocks₂₁) + x.toBlocks₂₂)
  exact ((continuous_const (y := Complex.I)).smul (continuous_toBlocks₂₁' (n := n))).neg.add
    (continuous_toBlocks₂₂' (n := n))
end PositivityTheory.Rg.Sw.LVs

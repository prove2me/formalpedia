-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.first_cayley_block_mul_inverse_cayley
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:47.41866+00:00
-- url     : https://prove2.me/submissions/8fb0da61-9b88-41c4-b01a-d3c04e2d7355

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_toBlocks___mul_03bb7bc462ab
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_toBlocks___mul_b314fdf1b50d

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
theorem _root_.solution (y : M2 n) : u1 (y * Cmi n) = y.toBlocks₂₁ := by
  rw [u1, toBlocks₂₁_mul, toBlocks₂₂_mul, Cmi]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, Matrix.mul_smul, Matrix.mul_one, smul_add, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring_nf
end PositivityTheory.Rg.Sw.LVs

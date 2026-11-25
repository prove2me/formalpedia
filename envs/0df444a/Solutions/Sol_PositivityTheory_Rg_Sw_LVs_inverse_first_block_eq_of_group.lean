-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.inverse_first_block_eq_of_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:41.180326+00:00
-- url     : https://prove2.me/submissions/c8a445c7-b152-4b38-86fa-f300e741ea89

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inv_eq_of_inG__f8fdb4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {g : M2 n} (hg : InG g) : ub1 g = (u1 g)ᴴ := by
  rw [ub1, inv_eq_of_inG hg, u1]
  conv_lhs => rw [← fromBlocks_toBlocks g]
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₁₁,
    toBlocks_fromBlocks₂₁, conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I]
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    zero_add, add_zero, neg_zero, neg_neg]
  module
end PositivityTheory.Rg.Sw.LVs

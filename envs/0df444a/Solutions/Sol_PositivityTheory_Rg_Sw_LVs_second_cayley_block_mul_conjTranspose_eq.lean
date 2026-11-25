-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.second_cayley_block_mul_conjTranspose_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:37.647275+00:00
-- url     : https://prove2.me/submissions/7d3c37f0-e6b8-4e73-859b-6744732ac14c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_lower_rel

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
theorem _root_.solution {g : M2 n} (hg : InG g) :
    u2 g * (u2 g)ᴴ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
  have h := lower_rel hg
  simp only [u2, conjTranspose_add, conjTranspose_neg, conjTranspose_smul, Complex.star_def, Complex.conj_I,
    Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h]
  match_scalars <;> simp [Complex.I_mul_I] <;> ring_nf <;> simp [Complex.I_sq]
end PositivityTheory.Rg.Sw.LVs

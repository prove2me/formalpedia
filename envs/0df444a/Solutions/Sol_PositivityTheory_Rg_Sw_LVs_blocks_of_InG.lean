-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.blocks_of_InG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:36.874415+00:00
-- url     : https://prove2.me/submissions/4983b0ac-7bd5-4f72-949d-04583d27334f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_mul_J_mul_of_InG

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
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {x : M2 n} (hx : InG x) :
    x.toBlocks₂₁ * (x.toBlocks₂₂)ᴴ = x.toBlocks₂₂ * (x.toBlocks₂₁)ᴴ ∧
      x.toBlocks₂₂ * (x.toBlocks₁₁)ᴴ - x.toBlocks₂₁ * (x.toBlocks₁₂)ᴴ = 1 := by
  have h := mul_J_mul_of_InG hx
  rw [← Matrix.fromBlocks_toBlocks x] at h
  simp only [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.mul_one,
    Matrix.mul_neg, zero_add, add_zero, Matrix.fromBlocks_inj] at h
  obtain ⟨-, -, h21, h22⟩ := h
  constructor
  · have := h22
    rw [Matrix.neg_mul, neg_add_eq_zero] at this
    exact this.symm
  · rw [Matrix.neg_mul, neg_add_eq_iff_eq_add] at h21
    rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add']
    rw [h21]; abel
end PositivityTheory.Rg.Sw.LVs

-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.det_u_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:35.354799+00:00
-- url     : https://prove2.me/submissions/f2c25df3-60e8-4815-8e3b-e5098615bbf5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_blocks_of_InG
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_u_mul_u_conj

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
theorem _root_.solution {x : M2 n} (hx : InG x) : (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0 := by
  have huu := u_mul_u_conj hx
  obtain ⟨-, h1⟩ := blocks_of_InG hx
  have h1' : x.toBlocks₁₁ * (x.toBlocks₂₂)ᴴ - x.toBlocks₁₂ * (x.toBlocks₂₁)ᴴ = 1 := by
    have := congrArg Matrix.conjTranspose h1
    simpa [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul] using this

  have key : ∀ v : Fin n → ℂ, (u1 x)ᴴ *ᵥ v = 0 → (u2 x)ᴴ *ᵥ v = 0 → v = 0 := by
    intro v e1 e2
    have hC : (x.toBlocks₂₁)ᴴ *ᵥ v = 0 := by
      have : (u2 x)ᴴ *ᵥ v - (u1 x)ᴴ *ᵥ v = (2 * Complex.I) • ((x.toBlocks₂₁)ᴴ *ᵥ v) := by
        simp only [u1, u2, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul,
          Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec, Complex.star_def, Complex.conj_I]
        module
      rw [e1, e2, sub_zero] at this
      exact (smul_eq_zero.1 this.symm).resolve_left (by simp)
    have hD : (x.toBlocks₂₂)ᴴ *ᵥ v = 0 := by
      have : (u2 x)ᴴ *ᵥ v + (u1 x)ᴴ *ᵥ v = (2 : ℂ) • ((x.toBlocks₂₂)ᴴ *ᵥ v) := by
        simp only [u1, u2, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul,
          Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec, Complex.star_def, Complex.conj_I]
        module
      rw [e1, e2, add_zero] at this
      exact (smul_eq_zero.1 this.symm).resolve_left (by norm_num)
    calc v = (x.toBlocks₁₁ * (x.toBlocks₂₂)ᴴ - x.toBlocks₁₂ * (x.toBlocks₂₁)ᴴ) *ᵥ v := by rw [h1', Matrix.one_mulVec]
      _ = 0 := by
        rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hC, hD, Matrix.mulVec_zero,
          Matrix.mulVec_zero, sub_zero]

  have other : ∀ (U V : Matrix (Fin n) (Fin n) ℂ), U * Uᴴ = V * Vᴴ → ∀ v : Fin n → ℂ, Uᴴ *ᵥ v = 0 → Vᴴ *ᵥ v = 0 := by
    intro U V hUV v hv
    have : star (Vᴴ *ᵥ v) ⬝ᵥ (Vᴴ *ᵥ v) = 0 := by
      rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← dotProduct_mulVec, Matrix.mulVec_mulVec,
        ← hUV, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, dotProduct_zero]
    exact dotProduct_star_self_eq_zero.1 this
  constructor
  · intro h0
    have h0' : ((u1 x)ᴴ).det = 0 := by rw [Matrix.det_conjTranspose, h0, star_zero]
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0'
    exact hv (key v hv0 (other _ _ huu v hv0))
  · intro h0
    have h0' : ((u2 x)ᴴ).det = 0 := by rw [Matrix.det_conjTranspose, h0, star_zero]
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0'
    exact hv (key v (other _ _ huu.symm v hv0) hv0)
end PositivityTheory.Rg.Sw.LVs

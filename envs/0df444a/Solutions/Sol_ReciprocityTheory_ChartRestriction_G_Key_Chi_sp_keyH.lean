-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.sp_keyH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:58:33.325802+00:00
-- url     : https://prove2.me/submissions/6a9d272c-50fc-4426-9b34-dd52c3d4f959

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_Blocks
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Key_Chi_blk_conjTranspose___ad3e91286297
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Key_Chi_blk_conjTranspose___9b0f0f02ddc5
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Key_Chi_blk_conjTranspose___0ce1162e1798
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Key_Chi_blk_conjTranspose___779a257255c5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    (jAut γ τ)ᴴ * nAut γ τ - (nAut γ τ)ᴴ * jAut γ τ = τ - τᴴ := by
  have h1 := SymplecticGroup.mem_iff'.mp hγ
  have h3 : (cMat γ)ᵀ * Matrix.J (Fin g) ℂ * cMat γ = Matrix.J (Fin g) ℂ := by
    have hJ : (Matrix.J (Fin g) ℤ).map (Int.castRingHom ℂ) = Matrix.J (Fin g) ℂ := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.J, Matrix.one_apply]
      all_goals (try split_ifs)
      all_goals (try simp_all)
    have := congrArg (fun M => M.map (Int.castRingHom ℂ)) h1
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hJ] at this
    exact this
  rw [← Matrix.fromBlocks_toBlocks (cMat γ), Matrix.J, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h3
  obtain ⟨e11, e12, e21, e22⟩ := Matrix.fromBlocks_inj.mp h3
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.zero_mul,
    Matrix.neg_mul, Matrix.one_mul] at e11 e12 e21 e22
  have hA := blk_conjTranspose₁₁ γ
  have hB := blk_conjTranspose₁₂ γ
  have hC := blk_conjTranspose₂₁ γ
  have hD := blk_conjTranspose₂₂ γ
  simp only [jAut, nAut]
  generalize (cMat γ).toBlocks₁₁ = A at e11 e12 e21 e22 hA hB hC hD ⊢
  generalize (cMat γ).toBlocks₁₂ = B at e11 e12 e21 e22 hA hB hC hD ⊢
  generalize (cMat γ).toBlocks₂₁ = C at e11 e12 e21 e22 hA hB hC hD ⊢
  generalize (cMat γ).toBlocks₂₂ = D at e11 e12 e21 e22 hA hB hC hD ⊢
  have e : (C * τ + D)ᴴ * (A * τ + B) - (A * τ + B)ᴴ * (C * τ + D) =
      τᴴ * (Cᵀ * A + -(Aᵀ * C)) * τ + τᴴ * (Cᵀ * B + -(Aᵀ * D) + 1) + (Dᵀ * A + -(Bᵀ * C) - 1) * τ +
        (Dᵀ * B + -(Bᵀ * D)) + (τ - τᴴ) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hA, hB, hC, hD]
    noncomm_ring
  rw [e, e11, e12, e21, e22]
  noncomm_ring
end ReciprocityTheory.ChartRestriction.G.Key.Chi

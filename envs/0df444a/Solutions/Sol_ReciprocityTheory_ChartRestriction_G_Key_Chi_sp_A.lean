-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.sp_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:25.150132+00:00
-- url     : https://prove2.me/submissions/8224f957-9a6b-4ec8-baba-1ad9f0bbb4f5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_Blocks
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_isSymm

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
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm)
    (hj : IsUnit (jAut γ τ).det) :
    (cMat γ).toBlocks₁₁ - spAct γ τ * (cMat γ).toBlocks₂₁ = ((jAut γ τ)⁻¹)ᵀ := by
  have hs := spAct_isSymm hγ hτ hj
  have hJt : IsUnit (jAut γ τ)ᵀ.det := by rwa [Matrix.det_transpose]
  have hσ : spAct γ τ = ((jAut γ τ)ᵀ)⁻¹ * (nAut γ τ)ᵀ := by
    rw [← hs.eq, show spAct γ τ = nAut γ τ * (jAut γ τ)⁻¹ from rfl, Matrix.transpose_mul,
      Matrix.transpose_nonsing_inv]
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
  obtain ⟨e11, _, e21, _⟩ := Matrix.fromBlocks_inj.mp h3
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.zero_mul,
    Matrix.neg_mul, Matrix.one_mul] at e11 e21
  have key : (jAut γ τ)ᵀ * ((cMat γ).toBlocks₁₁ - spAct γ τ * (cMat γ).toBlocks₂₁) = 1 := by
    rw [hσ, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJt,
      Matrix.one_mul]
    simp only [jAut, nAut]
    generalize (cMat γ).toBlocks₁₁ = A at e11 e21 ⊢
    generalize (cMat γ).toBlocks₁₂ = B at e11 e21 ⊢
    generalize (cMat γ).toBlocks₂₁ = C at e11 e21 ⊢
    generalize (cMat γ).toBlocks₂₂ = D at e11 e21 ⊢
    have e : (C * τ + D)ᵀ * A - (A * τ + B)ᵀ * C =
        τᵀ * (Cᵀ * A + -(Aᵀ * C)) + (Dᵀ * A + -(Bᵀ * C)) := by
      rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul]
      noncomm_ring
    rw [e, e11, e21, Matrix.mul_zero, zero_add]
  rw [Matrix.transpose_nonsing_inv]
  calc (cMat γ).toBlocks₁₁ - spAct γ τ * (cMat γ).toBlocks₂₁
      = ((jAut γ τ)ᵀ)⁻¹ * ((jAut γ τ)ᵀ * ((cMat γ).toBlocks₁₁ - spAct γ τ * (cMat γ).toBlocks₂₁)) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJt, Matrix.one_mul]
    _ = ((jAut γ τ)ᵀ)⁻¹ := by rw [key, Matrix.mul_one]
end ReciprocityTheory.ChartRestriction.G.Key.Chi

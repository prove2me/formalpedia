-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.sp_keyT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:27:03.415124+00:00
-- url     : https://prove2.me/submissions/bf4e584e-ede6-4816-b50d-80c1183c9673

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_Blocks
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm

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
    (jAut γ τ)ᵀ * nAut γ τ - (nAut γ τ)ᵀ * jAut γ τ = τ - τᵀ := by
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
  set A := (cMat γ).toBlocks₁₁
  set B := (cMat γ).toBlocks₁₂
  set C := (cMat γ).toBlocks₂₁
  set D := (cMat γ).toBlocks₂₂
  have e : (jAut γ τ)ᵀ * nAut γ τ - (nAut γ τ)ᵀ * jAut γ τ =
      τᵀ * (Cᵀ * A + -(Aᵀ * C)) * τ + τᵀ * (Cᵀ * B + -(Aᵀ * D) + 1) + (Dᵀ * A + -(Bᵀ * C) - 1) * τ +
        (Dᵀ * B + -(Bᵀ * D)) + (τ - τᵀ) := by
    simp only [jAut, nAut, Matrix.transpose_add, Matrix.transpose_mul]
    noncomm_ring
  rw [e, e11, e12, e21, e22]
  noncomm_ring
end ReciprocityTheory.ChartRestriction.G.Key.Chi

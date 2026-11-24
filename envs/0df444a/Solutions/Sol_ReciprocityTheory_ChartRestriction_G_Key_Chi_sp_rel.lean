-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.sp_rel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:37.746062+00:00
-- url     : https://prove2.me/submissions/57a3b1d1-efd0-4937-9571-cb1419a65127

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_InversionStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_Blocks

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
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    ((cMat γ).toBlocks₂₁ᵀ * (cMat γ).toBlocks₁₁ - (cMat γ).toBlocks₁₁ᵀ * (cMat γ).toBlocks₂₁ = 0) ∧
    ((cMat γ).toBlocks₂₁ᵀ * (cMat γ).toBlocks₁₂ - (cMat γ).toBlocks₁₁ᵀ * (cMat γ).toBlocks₂₂ = -1) ∧
    ((cMat γ).toBlocks₂₂ᵀ * (cMat γ).toBlocks₁₁ - (cMat γ).toBlocks₁₂ᵀ * (cMat γ).toBlocks₂₁ = 1) ∧
    ((cMat γ).toBlocks₂₂ᵀ * (cMat γ).toBlocks₁₂ - (cMat γ).toBlocks₁₂ᵀ * (cMat γ).toBlocks₂₂ = 0) := by
  rw [SymplecticGroup.mem_iff'] at hγ
  have h := congrArg (Int.castRingHom ℂ).mapMatrix hγ
  rw [map_mul, map_mul] at h
  have hc : (Int.castRingHom ℂ).mapMatrix γ = cMat γ := rfl
  have ht : (Int.castRingHom ℂ).mapMatrix γᵀ = (cMat γ)ᵀ := rfl
  have hJ : (Int.castRingHom ℂ).mapMatrix (Matrix.J (Fin g) ℤ) = Matrix.J (Fin g) ℂ :=
    Matrix.map_J (Fin g) (Int.castRingHom ℂ)
  rw [hc, ht, hJ] at h
  rw [← fromBlocks_toBlocks (cMat γ), fromBlocks_transpose, Matrix.J, fromBlocks_multiply,
    fromBlocks_multiply] at h
  obtain ⟨e11, e12, e21, e22⟩ := Matrix.fromBlocks_inj.mp h
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
    zero_add, add_zero] at e11 e12 e21 e22
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e11]; abel
  · rw [← e12]; abel
  · rw [← e21]; abel
  · rw [← e22]; abel
end ReciprocityTheory.ChartRestriction.G.Key.Chi

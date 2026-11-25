-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.expArg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:30:04.860985+00:00
-- url     : https://prove2.me/submissions/8230ce99-2302-443f-86a4-131e8999b970

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_InversionStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_Blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_cMat_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_blocks_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_dot_conj

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
theorem _root_.solution {g : ℕ} (γ δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (τ : Matrix (Fin g) (Fin g) ℂ) (hδ : IsUnit (jAut δ τ).det)
    (hγ : IsUnit (jAut γ (spAct δ τ)).det)
    (hA : (cMat δ).toBlocks₁₁ - spAct δ τ * (cMat δ).toBlocks₂₁ = ((jAut δ τ)⁻¹)ᵀ)
    (z : Fin g → ℂ) :
    expArg (γ * δ) τ z = expArg γ (spAct δ τ) (zAct δ τ z) + expArg δ τ z := by
  obtain ⟨-, -, h21, -⟩ := blocks_mul (cMat γ) (cMat δ)
  have hN : (cMat δ).toBlocks₁₁ = ((jAut δ τ)⁻¹)ᵀ + spAct δ τ * (cMat δ).toBlocks₂₁ :=
    sub_eq_iff_eq_add.mp hA
  have hM : (cMat γ).toBlocks₂₁ * (cMat δ).toBlocks₁₁ + (cMat γ).toBlocks₂₂ * (cMat δ).toBlocks₂₁ =
      (cMat γ).toBlocks₂₁ * ((jAut δ τ)⁻¹)ᵀ + jAut γ (spAct δ τ) * (cMat δ).toBlocks₂₁ := by
    rw [hN, jAut_eq γ]
    noncomm_ring
  have key : (jAut (γ * δ) τ)⁻¹ * (cMat (γ * δ)).toBlocks₂₁ =
      (jAut δ τ)⁻¹ * ((jAut γ (spAct δ τ))⁻¹ * (cMat γ).toBlocks₂₁) * ((jAut δ τ)⁻¹)ᵀ +
        (jAut δ τ)⁻¹ * (cMat δ).toBlocks₂₁ := by
    rw [jAut_mul γ δ τ hδ, Matrix.mul_inv_rev, cMat_mul, h21, hM]
    simp only [Matrix.mul_add, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hγ]
  rw [expArg, key, Matrix.add_mulVec, dotProduct_add, dot_conj]
  rfl
end ReciprocityTheory.ChartRestriction.G.Key.Chi

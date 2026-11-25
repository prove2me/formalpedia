-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.nAut_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:15:59.621198+00:00
-- url     : https://prove2.me/submissions/3b71451e-a831-420f-bae3-297333cf2676

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_InversionStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_Blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_nAut_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_cMat_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_blocks_mul

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
    (τ : Matrix (Fin g) (Fin g) ℂ) (h : IsUnit (jAut δ τ).det) :
    nAut (γ * δ) τ = nAut γ (spAct δ τ) * jAut δ τ := by
  obtain ⟨h11, h12, -, -⟩ := blocks_mul (cMat γ) (cMat δ)
  have hj : (jAut δ τ)⁻¹ * jAut δ τ = 1 := Matrix.nonsing_inv_mul _ h
  rw [spAct_eq, nAut_eq γ, add_mul, Matrix.mul_assoc _ (nAut δ τ * _), Matrix.mul_assoc (nAut δ τ),
    hj, Matrix.mul_one]
  rw [nAut_eq (γ * δ), cMat_mul, h11, h12, nAut_eq δ, jAut_eq δ]
  noncomm_ring
end ReciprocityTheory.ChartRestriction.G.Key.Chi

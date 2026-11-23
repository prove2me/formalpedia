-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:46.688897+00:00
-- url     : https://prove2.me/submissions/58651e6a-5f33-47a5-80f9-8369dd19b1e4

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
    jAut (γ * δ) τ = jAut γ (spAct δ τ) * jAut δ τ := by
  obtain ⟨-, -, h21, h22⟩ := blocks_mul (cMat γ) (cMat δ)
  have hj : (jAut δ τ)⁻¹ * jAut δ τ = 1 := Matrix.nonsing_inv_mul _ h
  rw [spAct_eq, jAut_eq γ, add_mul, Matrix.mul_assoc _ (nAut δ τ * _), Matrix.mul_assoc (nAut δ τ),
    hj, Matrix.mul_one]
  rw [jAut_eq (γ * δ), cMat_mul, h21, h22, nAut_eq δ, jAut_eq δ]
  noncomm_ring
end ReciprocityTheory.ChartRestriction.G.Key.Chi

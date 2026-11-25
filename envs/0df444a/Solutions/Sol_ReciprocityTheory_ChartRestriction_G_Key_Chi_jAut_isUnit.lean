-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:24.61481+00:00
-- url     : https://prove2.me/submissions/a11a7e92-0f52-420d-8584-b9e4ffaa2ce9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_Blocks
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_sub_conjTranspose_of_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_re_pos_of_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_sp_keyH

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
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) : IsUnit (jAut γ τ).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hpos := re_pos_of_posDef hτ.2 hv
  have h0 : star v ⬝ᵥ (((jAut γ τ)ᴴ * nAut γ τ - (nAut γ τ)ᴴ * jAut γ τ) *ᵥ v) = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hJv,
      Matrix.mulVec_zero, dotProduct_zero, sub_zero, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hJv,
      star_zero, zero_dotProduct]
  rw [sp_keyH hγ τ, sub_conjTranspose_of_symm hτ.1, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    mul_eq_zero] at h0
  rcases h0 with h | h
  · simp at h
  · rw [show (τ.map Complex.im).map (fun x : ℝ => (x : ℂ)) = imC τ from rfl, h] at hpos
    simp at hpos
end ReciprocityTheory.ChartRestriction.G.Key.Chi

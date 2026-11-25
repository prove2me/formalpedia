-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.chiU_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:26:59.87145+00:00
-- url     : https://prove2.me/submissions/867f8f09-09b0-44ea-9a1d-e76cdbecdab7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_eC_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_ofRealVec_halfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_ofIntVec_dot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_cMat_J
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_J
import Theorems.Thm_ReciprocityTheory_PTheta_eC_int


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
theorem _root_.solution {g : ℕ} (hInv : InversionStatement) : ChiAtU g (Matrix.J (Fin g) ℤ) := by
  intro n n'
  have hd : ofRealVec (halfVec (-n')) ⬝ᵥ ofRealVec (halfVec n) = (((-n') ⬝ᵥ n : ℤ) : ℂ) / 4 := by
    rw [ofRealVec_halfVec, ofRealVec_halfVec, smul_dotProduct, dotProduct_smul, ofIntVec_dot]
    simp only [smul_eq_mul]
    ring
  refine ⟨-n', n, (-I) ^ g * eC (2 * (ofRealVec (halfVec (-n')) ⬝ᵥ ofRealVec (halfVec n))), ?_, ?_⟩
  · have h4 : (-I) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, neg_sq, I_sq]
      norm_num
    rw [mul_pow, ← pow_mul, mul_comm g 4, pow_mul, h4, one_pow, one_mul, eC_pow, hd]
    convert eC_int (2 * ((-n') ⬝ᵥ n)) using 2
    push_cast
    ring
  · intro τ hτ z
    have hsym : τᵀ = τ := hτ.1
    have hz : zAct (Matrix.J (Fin g) ℤ) τ z = τ⁻¹ *ᵥ z := by
      rw [zAct, jAut_J, Matrix.transpose_nonsing_inv, hsym]
    have hs : spAct (Matrix.J (Fin g) ℤ) τ = -τ⁻¹ := by
      rw [spAct, jAut_J, cMat_J]
      simp [Matrix.J]
    have hx : expArg (Matrix.J (Fin g) ℤ) τ z = z ⬝ᵥ (τ⁻¹ *ᵥ z) := by
      rw [expArg, jAut_J, cMat_J]
      simp [Matrix.J]
    have hneg : -halfVec (-n') = halfVec n' := by
      funext i
      simp [halfVec, neg_div]
    rw [hz, hs, hx, jAut_J, hInv g (halfVec (-n')) (halfVec n) τ hτ z, hneg]
    ring
end ReciprocityTheory.ChartRestriction.G.Key.Chi

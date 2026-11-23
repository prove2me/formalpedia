-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.zAct_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:02.316889+00:00
-- url     : https://prove2.me/submissions/cb59a02b-19fc-4a82-8fc0-ef6f59e747e1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_InversionStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_Blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_mul

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
    (τ : Matrix (Fin g) (Fin g) ℂ) (h : IsUnit (jAut δ τ).det) (z : Fin g → ℂ) :
    zAct (γ * δ) τ z = zAct γ (spAct δ τ) (zAct δ τ z) := by
  simp only [zAct, jAut_mul γ δ τ h, Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.mulVec_mulVec]
end ReciprocityTheory.ChartRestriction.G.Key.Chi

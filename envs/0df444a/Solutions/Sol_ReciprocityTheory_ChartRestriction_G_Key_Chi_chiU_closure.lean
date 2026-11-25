-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.chiU_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:39:09.378879+00:00
-- url     : https://prove2.me/submissions/e3b32b51-7d5a-4b12-ab81-39bb5d287f04

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_chiU_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_one_eq_spTransl_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_chiU_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_chiU_spTransl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spGens_subset


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
theorem _root_.solution {g : ℕ} (hInv : InversionStatement)
    {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} (hγ : γ ∈ Submonoid.closure (spGens g)) :
    γ ∈ Matrix.symplecticGroup (Fin g) ℤ ∧ ChiAtU g γ := by
  induction hγ using Submonoid.closure_induction with
  | mem x hx => exact ⟨spGens_subset g hx, chiU_gen hInv hx⟩
  | one =>
    refine ⟨one_mem _, ?_⟩
    rw [one_eq_spTransl_zero]
    exact chiU_spTransl 0 Matrix.isSymm_zero
  | mul x y _ _ hx hy => exact ⟨mul_mem hx.1 hy.1, chiU_mul hx.1 hy.1 hx.2 hy.2⟩
end ReciprocityTheory.ChartRestriction.G.Key.Chi

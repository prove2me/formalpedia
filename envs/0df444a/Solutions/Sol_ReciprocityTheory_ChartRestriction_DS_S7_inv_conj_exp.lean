-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.inv_conj_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:18:08.771312+00:00
-- url     : https://prove2.me/submissions/99bb04bf-b04b-4140-b7f1-2dd43b26b7b6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExistsMu
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiMExpFormula
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_inv_mul__4f9184a765fd
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_mul_inv__47a4d626f289


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ) :
    (toMK k⁻¹ * NormedSpace.exp X * toMK k)⁻¹ = toMK k⁻¹ * NormedSpace.exp (-X) * toMK k := by
  apply Matrix.inv_eq_left_inv
  have hexp : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
      NormedSpace.exp_zero]
  calc toMK k⁻¹ * NormedSpace.exp (-X) * toMK k * (toMK k⁻¹ * NormedSpace.exp X * toMK k)
      = toMK k⁻¹ * NormedSpace.exp (-X) * (toMK k * toMK k⁻¹) * NormedSpace.exp X * toMK k := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [toMK_mul_inv', Matrix.mul_one, Matrix.mul_assoc (toMK k⁻¹), hexp, Matrix.mul_one,
          toMK_inv_mul']
end ReciprocityTheory.ChartRestriction.DS.S7

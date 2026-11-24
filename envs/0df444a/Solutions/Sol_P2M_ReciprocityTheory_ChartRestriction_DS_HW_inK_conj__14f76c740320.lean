-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_inK_conj__14f76c740320
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:17:51.443369+00:00
-- url     : https://prove2.me/submissions/9467cab0-dc73-4ea7-b65c-fb753c76b2f3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_HW_inK_iff__24a5ac304dfc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ε : Fin n → Bool} (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    inK ε (toMK k * Y * star (toMK k)) := by
  rw [inK_iff'] at hY ⊢
  have hK := k.2.2
  have hK' : star (toMK k) * Jm ε = Jm ε * star (toMK k) := (Kset_star ε k.2).2
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hY.1]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_assoc]
  · calc toMK k * Y * star (toMK k) * Jm ε = toMK k * (Y * (star (toMK k) * Jm ε)) := by
          simp only [Matrix.mul_assoc]
      _ = toMK k * (Y * (Jm ε * star (toMK k))) := by rw [hK']
      _ = toMK k * ((Y * Jm ε) * star (toMK k)) := by simp only [Matrix.mul_assoc]
      _ = toMK k * ((Jm ε * Y) * star (toMK k)) := by rw [hY.2]
      _ = (toMK k * Jm ε) * Y * star (toMK k) := by simp only [Matrix.mul_assoc]
      _ = Jm ε * toMK k * Y * star (toMK k) := by rw [hK]
      _ = Jm ε * (toMK k * Y * star (toMK k)) := by simp only [Matrix.mul_assoc]
end ReciprocityTheory.ChartRestriction.DS.HW

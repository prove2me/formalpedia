-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_HW_inK_iff__24a5ac304dfc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:00:09.477724+00:00
-- url     : https://prove2.me/submissions/0ce40bf1-e90e-41b2-b7b9-6522db9d2808

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
import Theorems.Thm_Formalism_REAL_Jm_mul_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Jm_mul_self


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
theorem _root_.solution (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inK ε X ↔ Xᴴ = -X ∧ X * Jm ε = Jm ε * X := by
  constructor
  · rintro ⟨hG, hC⟩
    refine ⟨?_, hC⟩
    have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by
      rw [hC]; exact eq_neg_of_add_eq_zero_left hG
    have h2 := congrArg (· * Jm ε) h1
    simp only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one, Matrix.neg_mul] at h2
    exact h2
  · rintro ⟨hH, hC⟩
    refine ⟨?_, hC⟩
    unfold inG
    rw [hH, Matrix.neg_mul, hC, neg_add_cancel]
end ReciprocityTheory.ChartRestriction.DS.HW

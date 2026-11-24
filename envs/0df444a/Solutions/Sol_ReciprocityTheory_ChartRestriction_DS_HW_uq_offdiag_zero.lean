-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.uq_offdiag_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:34:15.669808+00:00
-- url     : https://prove2.me/submissions/52e08358-c72a-4011-85cd-afbe3a310129

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Weight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Unique

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X)
    {a b : Fin n} (hab : ε a ≠ ε b) : X a b = 0 := by
  have hd : (if ε a then (1 : ℂ) else -1) ≠ (if ε b then (1 : ℂ) else -1) := by
    cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at hab ⊢ <;> norm_num
  have h := congrFun (congrFun hX a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have h2 : X a b * ((if ε b then (1 : ℂ) else -1) - (if ε a then (1 : ℂ) else -1)) = 0 := by
    rw [mul_sub, h]; ring
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.mp h3).symm hd
end ReciprocityTheory.ChartRestriction.DS.HW

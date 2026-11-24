-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.inK_entry_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:57:22.400886+00:00
-- url     : https://prove2.me/submissions/0821abca-5be1-4832-86ec-c0b5d9732708

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm

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
theorem _root_.solution {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y)
    {a b : Fin n} (hab : ε a ≠ ε b) : Y a b = 0 := by
  obtain ⟨-, h2⟩ := hY
  have h := congrFun (congrFun h2 a) b
  unfold Jm at h
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at hab h <;>
    first
    | exact h
    | linear_combination (1 / 2 : ℂ) * h
    | linear_combination (-1 / 2 : ℂ) * h
end ReciprocityTheory.ChartRestriction.DS.HW

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.single_mul_Jm_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:58:43.360965+00:00
-- url     : https://prove2.me/submissions/fc37cf9a-1426-4a3c-b85d-32787157129a

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
theorem _root_.solution {ε : Fin n → Bool} {a b : Fin n} (hab : ε a = ε b) (c : ℂ) :
    Matrix.single a b c * Jm ε = Jm ε * Matrix.single a b c := by
  unfold Jm
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : a = i
  · by_cases hj : b = j
    · subst hi
      subst hj
      simp only [hab]
      ring
    · simp [Matrix.single_apply, hj]
  · simp [Matrix.single_apply, hi]
end ReciprocityTheory.ChartRestriction.DS.HW

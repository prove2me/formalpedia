-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.single_mul_Jm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:00:09.504475+00:00
-- url     : https://prove2.me/submissions/fe469cdd-6620-4e84-ab16-fd526d40e5cf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex

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
theorem _root_.solution {ε : Fin n → Bool} {a b : Fin n} (h : ε a = ε b) (c : ℂ) :
    Matrix.single a b c * Jm ε = Jm ε * Matrix.single a b c := by
  ext i j
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases hi : a = i <;> by_cases hj : b = j
  · subst hi hj; simp [h, mul_comm]
  all_goals simp [hi, hj]
end ReciprocityTheory.ChartRestriction.DS.HW

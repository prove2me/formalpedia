-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InhabA.eq_zero_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:57.68469+00:00
-- url     : https://prove2.me/submissions/2043dfdf-04db-4015-aa82-ffbdb7eb722f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_Lemmata_MovedPointExistence_ExistsMoved
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.S7.InhabA
open ReciprocityTheory.ChartRestriction.DS
variable {m : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.InhabA
theorem _root_.solution {ε : Fin m → Bool} {g : Matrix (Fin m) (Fin m) ℂ} (hg : g * Jm ε = Jm ε * g)
    (i j : Fin m) (hij : ε i ≠ ε j) : g i j = 0 := by
  have h := congrFun (congrFun hg i) j
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  cases hi : ε i <;> cases hj : ε j
  · exact absurd (hi.trans hj.symm) hij
  · simp only [hi, hj, Bool.false_eq_true, if_false, if_true] at h
    linear_combination h / 2
  · simp only [hi, hj, Bool.false_eq_true, if_false, if_true] at h
    linear_combination -h / 2
  · exact absurd (hi.trans hj.symm) hij
end ReciprocityTheory.ChartRestriction.DS.S7.InhabA

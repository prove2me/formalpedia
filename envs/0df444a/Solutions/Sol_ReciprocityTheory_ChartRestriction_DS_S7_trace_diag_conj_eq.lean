-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.trace_diag_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:08:11.697608+00:00
-- url     : https://prove2.me/submissions/9bad7cee-1ff5-4456-bed8-e41f809e936a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_Ye

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {U Y : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (i : ℕ) :
    ∑ k, (y k : ℂ) * dmK U i k k = ∑ a, dmChi i a * Y a a := by
  simp only [dmK, Finset.mul_sum, dm_Ye hY]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.DS.S7

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CasPsA.conj_single_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:11.024865+00:00
-- url     : https://prove2.me/submissions/196a62b5-820b-4d92-b722-27641b9bd37f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsA_entry_conj_single

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
open ReciprocityTheory.ChartRestriction.DS.S7.CasPsA
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.CasPsA
theorem _root_.solution (u v : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    u * Matrix.single a b (1 : ℂ) * v = ∑ c, ∑ d, (u c a * v b d) • Matrix.single c d (1 : ℂ) := by
  ext i j
  rw [entry_conj_single]
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
end ReciprocityTheory.ChartRestriction.DS.S7.CasPsA

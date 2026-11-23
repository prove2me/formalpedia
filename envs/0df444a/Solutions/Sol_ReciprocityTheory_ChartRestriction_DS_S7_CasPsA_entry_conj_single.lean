-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CasPsA.entry_conj_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:28.418797+00:00
-- url     : https://prove2.me/submissions/18bd18bd-7636-4120-ae52-22e2e847c01e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA

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
theorem _root_.solution (u v : Matrix (Fin n) (Fin n) ℂ) (a b i j : Fin n) :
    (u * Matrix.single a b (1 : ℂ) * v) i j = u i a * v b j := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
end ReciprocityTheory.ChartRestriction.DS.S7.CasPsA

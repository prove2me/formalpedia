-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.decA_hs_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:15:12.039895+00:00
-- url     : https://prove2.me/submissions/ae172aa4-7eb4-4672-a596-bbce78a3bfe0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMoments
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecALogLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (A : Matrix (Fin n) (Fin n) ℂ) : ((hs A : ℝ) : ℂ) = Matrix.trace (A * Aᴴ) := by
  unfold hs
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl
end ReciprocityTheory.ChartRestriction.DS.S7

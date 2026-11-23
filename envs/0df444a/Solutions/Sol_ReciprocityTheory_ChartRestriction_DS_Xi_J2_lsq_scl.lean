-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.lsq_scl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:27.018805+00:00
-- url     : https://prove2.me/submissions/550f991b-5d66-4322-b2e4-5dc98d9d4eb5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution {p m : ℕ} (a0 : ℂ) (r : ℝ) (hr : 1 + ‖a0‖ ^ 2 = r ^ 2) (x : Xp p m) (i : Fin (p + 1)) :
    Lsq (tailPt (sclPt a0 r x)) i.succ = r ^ 2 * Lsq x i := by
  simp only [Lsq, tailPt, sclPt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [Nat.zero_lt_succ, if_true, add_lt_add_iff_right, mul_add, Finset.mul_sum, mul_ite, mul_zero]
  linarith
end ReciprocityTheory.ChartRestriction.DS.Xi.J2

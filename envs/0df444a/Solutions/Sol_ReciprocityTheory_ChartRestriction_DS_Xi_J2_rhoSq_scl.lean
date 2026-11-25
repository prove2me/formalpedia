-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.rhoSq_scl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:11.330696+00:00
-- url     : https://prove2.me/submissions/ea3aedbf-f03b-4211-8e4d-8eaee9635ce0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_lsq_scl

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
    rhoSq (tailPt (sclPt a0 r x)) i.succ = r ^ 2 * rhoSq x i := by
  have hl := lsq_scl a0 r hr x (Fin.last p)
  rw [Fin.succ_last] at hl
  unfold rhoSq
  rw [hl]
  simp only [tailPt, sclPt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [add_le_add_iff_right, mul_add, Finset.mul_sum, mul_ite, mul_zero]
  simp
end ReciprocityTheory.ChartRestriction.DS.Xi.J2

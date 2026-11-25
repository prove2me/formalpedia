-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.bco_scl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:09.736041+00:00
-- url     : https://prove2.me/submissions/83ca1a05-1f70-4d43-a83a-96d42c90b1fc

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
theorem _root_.solution {p m : ℕ} (a0 : ℂ) (r : ℝ) (x : Xp p m) (i : Fin (p + 1)) :
    bco (tailPt (sclPt a0 r x)) i.succ = ((r ^ 2 : ℝ) : ℂ) * bco x i := by
  simp only [bco, tailPt, sclPt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [add_le_add_iff_right, Complex.real_smul, star_mul',
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  simp
  have s1 : ∑ j, (r : ℂ) ^ 2 * ((‖x.2.2.1 j‖ : ℂ)) ^ 2 = (r : ℂ) ^ 2 * ∑ j, ((‖x.2.2.1 j‖ : ℂ)) ^ 2 := by
    rw [Finset.mul_sum]
  have s2 : (∑ j : Fin p, if (i : ℕ) ≤ (j : ℕ) then (r : ℂ) * x.2.1 j * ((r : ℂ) * (starRingEnd ℂ) (x.1 j)) else 0)
      = (r : ℂ) ^ 2 * ∑ j : Fin p, if (i : ℕ) ≤ (j : ℕ) then x.2.1 j * (starRingEnd ℂ) (x.1 j) else 0 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; split_ifs <;> ring
  rw [s1, s2]; ring
end ReciprocityTheory.ChartRestriction.DS.Xi.J2

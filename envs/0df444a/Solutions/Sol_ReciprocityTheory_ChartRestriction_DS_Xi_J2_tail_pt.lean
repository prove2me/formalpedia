-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.tail_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:31:15.385215+00:00
-- url     : https://prove2.me/submissions/22a6ce11-f3f0-4e91-a37e-17e72cacdcbd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_criticalExponent_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_prod_update
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_de_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_de_scl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_lsq_scl_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ) (a0 : ℂ) (t : ℝ) (hr : 1 + ‖a0‖ ^ 2 = t ^ 2)
    (q : Xp p m) :
    tailF p m α ν (sclPt a0 t q) =
      ENNReal.ofReal ((1 + ‖a0‖ ^ 2) ^ ((-2 + α) / 2 - α - ∑ i, (s0N p m i + ν i))) *
        chF p m (Function.update ν 0 (α + ν 0)) q := by
  have hL : 0 < 1 + ‖a0‖ ^ 2 := by positivity
  unfold tailF chF
  rw [lsq_scl_one, ← Fin.succ_zero_eq_one, de_scl a0 t hr q 0]
  simp only [de_scl a0 t hr q, criticalExponent_succ]
  rw [← hr, ← ENNReal.ofReal_prod_of_nonneg
      (fun i _ => Real.rpow_nonneg (mul_nonneg hL.le (de_pos q i).le) _),
    ← ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (de_pos q l).le _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hL.le _)
      (Real.rpow_nonneg (mul_nonneg hL.le (de_pos q 0).le) _)),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)]
  congr 1
  rw [prod_update (de q) (s0N p m) ν (de_pos q) α,
    Finset.prod_congr rfl fun i _ => Real.mul_rpow hL.le (de_pos q i).le, Finset.prod_mul_distrib,
    ← Real.rpow_sum_of_pos hL, Real.mul_rpow hL.le (de_pos q 0).le]
  rw [show (-2 + α) / 2 - α - ∑ i, (s0N p m i + ν i) = (-2 + α) / 2 + -α + ∑ i, -(s0N p m i + ν i) by
    rw [Finset.sum_neg_distrib]; ring, Real.rpow_add hL, Real.rpow_add hL]
  ring
end ReciprocityTheory.ChartRestriction.DS.Xi.J2

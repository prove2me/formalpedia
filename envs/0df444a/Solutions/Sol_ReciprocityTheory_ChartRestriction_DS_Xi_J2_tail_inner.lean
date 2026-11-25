-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.tail_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:41:57.527253+00:00
-- url     : https://prove2.me/submissions/10f9b2be-2076-4820-93d8-d731847b5248

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_chF_meas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_tailF_meas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_sum_s0N
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_tail_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_cont_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_lint_scl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_sclL_apply


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
theorem _root_.solution (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ) (a0 : ℂ) :
    ∫⁻ q : Xp p m, tailF p m α ν (Fin.cons a0 q.1, q.2) =
      ENNReal.ofReal ((1 + ‖a0‖ ^ 2) ^ (-(2 + α + 2 * ∑ i, ν i) / 2)) *
        CHInt p m (Function.update ν 0 (α + ν 0)) := by
  have hL : 0 < 1 + ‖a0‖ ^ 2 := by positivity
  set t := Real.sqrt (1 + ‖a0‖ ^ 2) with ht_def
  have ht : 0 < t := Real.sqrt_pos.2 hL
  have htt : 1 + ‖a0‖ ^ 2 = t ^ 2 := (Real.sq_sqrt hL.le).symm
  have hc : Continuous fun q : Xp p m => ((Fin.cons a0 q.1, q.2) : TDom p m) :=
    (cont_cons.comp (continuous_const.prodMk continuous_fst)).prodMk continuous_snd
  have hG : Measurable fun q : Xp p m => tailF p m α ν (Fin.cons a0 q.1, q.2) :=
    (tailF_meas p m α ν).comp hc.measurable
  have hpt : ∀ x : Xp p m, tailF p m α ν (Fin.cons a0 (sclL p m t x).1, (sclL p m t x).2) =
      tailF p m α ν (sclPt a0 t x) := fun x => by rw [sclL_apply]; rfl
  rw [lint_scl hG ht]
  simp only [hpt, tail_pt p m α ν a0 t htt]
  rw [lintegral_const_mul _ (chF_meas _ _ _), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hreal : t ^ (4 * p + 2 * m + 2) * (1 + ‖a0‖ ^ 2) ^ ((-2 + α) / 2 - α - ∑ i, (s0N p m i + ν i)) =
      (1 + ‖a0‖ ^ 2) ^ (-(2 + α + 2 * ∑ i, ν i) / 2) := by
    rw [show 4 * p + 2 * m + 2 = 2 * (2 * p + m + 1) by ring, pow_mul, ← htt, ← Real.rpow_natCast,
      ← Real.rpow_add hL, Finset.sum_add_distrib, sum_s0N]
    congr 1
    push_cast
    ring
  rw [hreal]
  rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.J2

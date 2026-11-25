-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.hon_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:50:43.115095+00:00
-- url     : https://prove2.me/submissions/7ff75b85-debd-454f-a295-11e905447d13

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_partialYAtZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_partialYAtZero_atX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_partialYAtZero_atY
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_partialYAtZero_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_coeffY_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_deriv_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_deriv_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (h : LawD lam Φ) (x : K) (D : PowerSeries K)
    (hadd : DivByMv x (D.subst Φ - atX D - atY D)) :
    DivBy x (derivative K D - C (coeff 1 D) * derivative K lam) := by
  have h1 := divBy_partialYAtZero hadd
  rw [partialYAtZero_sub, partialYAtZero_sub, h.coeffY_subst, partialYAtZero_atX, partialYAtZero_atY, sub_zero] at h1
  have e : derivative K D - C (coeff 1 D) * derivative K lam =
      derivative K lam * (derivative K D * d2 Φ - C (coeff 1 D)) := by
    linear_combination (-derivative K D) * h.deriv_mul
  rw [e]
  have hl := h.deriv_integral
  unfold DivBy at h1 ⊢
  unfold IntegralPS at hl
  intro n
  rw [coeff_mul]
  refine Finset.sum_induction _ (fun y => ‖y‖ ≤ ‖x‖)
    (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
    (by simp) fun p _ => ?_
  rw [norm_mul]
  calc ‖coeff p.1 (derivative K lam)‖ * ‖coeff p.2 (derivative K D * d2 Φ - C (coeff 1 D))‖
        ≤ 1 * ‖x‖ := mul_le_mul (hl _) (h1 _) (norm_nonneg _) zero_le_one
    _ = ‖x‖ := one_mul _
end ReciprocityTheory.ChartRestriction.L1

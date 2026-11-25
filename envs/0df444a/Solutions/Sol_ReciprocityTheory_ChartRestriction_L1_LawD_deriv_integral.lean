-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.LawD.deriv_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:28:08.07651+00:00
-- url     : https://prove2.me/submissions/d055e8cf-5ddb-4dc0-8a42-86f248eee669

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_partialYAtZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_deriv_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_deriv_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_constantCoeff_partialYAtZero

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
namespace LawD
theorem _root_.solution (h : LawD lam Φ) : IntegralPS (derivative K lam) := by
  have hm := h.deriv_mul
  have ha := integralPS_partialYAtZero h.Φint
  have h0 := h.constantCoeff_partialYAtZero
  unfold IntegralPS at ha ⊢
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [h.deriv_const]
    · have hc := congrArg (coeff n) hm
      simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
        Nat.sub_self, coeff_zero_eq_constantCoeff_apply, h0, mul_one, coeff_one,
        if_neg (show n ≠ 0 by omega)] at hc
      have e : coeff n (derivative K lam) =
          -∑ k ∈ Finset.range n, coeff k (derivative K lam) * coeff (n - k) (d2 Φ) := by
        linear_combination hc
      rw [e, norm_neg]
      refine Finset.sum_induction _ (fun x => ‖x‖ ≤ 1)
        (fun x y hx hy => (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy))
        (by simp) fun k hk => ?_
      rw [norm_mul]
      have hk' := Finset.mem_range.mp hk
      calc ‖coeff k (derivative K lam)‖ * ‖coeff (n - k) (d2 Φ)‖ ≤ 1 * 1 :=
            mul_le_mul (ih k hk') (ha _) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
end LawD
end ReciprocityTheory.ChartRestriction.L1

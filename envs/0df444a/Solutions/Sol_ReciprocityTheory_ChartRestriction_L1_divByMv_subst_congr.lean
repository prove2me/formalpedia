-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divByMv_subst_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:54:13.150777+00:00
-- url     : https://prove2.me/submissions/0668468f-69fe-4b42-89d9-963bab260eda

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_iff_divBy_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_iff_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]
section Ring
variable {ι : Type}
end Ring
section OneVar
end OneVar
section Subst
variable {ι : Type}
private theorem norm_finsum_le_of_forall_norm_le {α : Type} (g : α → K) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖g i‖ ≤ C) : ‖∑ᶠ i, g i‖ ≤ C := by
  by_cases hs : (Function.support g).Finite
  · rw [finsum_eq_sum g hs]
    exact Finset.sum_induction _ (fun z : K => ‖z‖ ≤ C)
      (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
      (by rw [norm_zero]; exact hC) (fun i _ => h i)
  · rw [finsum_of_infinite_support hs, norm_zero]
    exact hC
end Subst
section Frob
variable {l : ℕ} {σ : K →+* K} {ι : Type}
end Frob
end ReciprocityTheory.ChartRestriction.L1
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable {ι : Type}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {x : K} (hx : ‖x‖ ≤ 1) {f : PowerSeries K} {P Q : MvPowerSeries ι K}
    (hf : IntegralPS f) (hP0 : MvPowerSeries.constantCoeff P = 0)
    (hQ0 : MvPowerSeries.constantCoeff Q = 0) (hP : IntegralMv P) (hQ : IntegralMv Q)
    (hPQ : DivByMv x (P - Q)) : DivByMv x (f.subst P - f.subst Q) := by
  by_cases hx : x = 0
  · subst hx
    have hPQ' : P = Q := by
      ext d
      have h1 := hPQ d
      rw [norm_zero, map_sub] at h1
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)
    rw [hPQ', sub_self]
    exact divByMv_zero _
  obtain ⟨R, hR, hPR⟩ := (divByMv_iff_smul hx _).mp hPQ
  have haP : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  have haQ : PowerSeries.HasSubst Q := PowerSeries.HasSubst.of_constantCoeff_zero hQ0
  have hf' : ∀ k, ‖coeff k f‖ ≤ 1 := hf
  intro d
  have hfinP := PowerSeries.coeff_subst_finite haP f d
  have hfinQ := PowerSeries.coeff_subst_finite haQ f d
  rw [map_sub, PowerSeries.coeff_subst haP, PowerSeries.coeff_subst haQ,
    ← finsum_sub_distrib hfinP hfinQ]
  refine norm_finsum_le_of_forall_norm_le _ (norm_nonneg _) fun k => ?_
  have hG : IntegralMv (∑ i ∈ Finset.range k, P ^ i * Q ^ (k - 1 - i)) := by
    rw [integralMv_iff_divBy_one]
    exact divByMv_sum _ _ fun i _ =>
      (integralMv_iff_divBy_one _).mp (integralMv_mul (integralMv_pow hP i) (integralMv_pow hQ _))
  have hGR := (integralMv_iff_divBy_one _).mp (integralMv_mul hG hR) d
  rw [norm_one] at hGR
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub, ← geom_sum₂_mul, hPR, mul_smul_comm,
    MvPowerSeries.coeff_smul, norm_mul, norm_mul]
  calc ‖coeff k f‖ * (‖x‖ * ‖MvPowerSeries.coeff d ((∑ i ∈ Finset.range k, P ^ i * Q ^ (k - 1 - i)) * R)‖)
      ≤ 1 * (‖x‖ * 1) := mul_le_mul (hf' k) (mul_le_mul_of_nonneg_left hGR (norm_nonneg _))
        (by positivity) zero_le_one
    _ = ‖x‖ := by ring
end ReciprocityTheory.ChartRestriction.L1

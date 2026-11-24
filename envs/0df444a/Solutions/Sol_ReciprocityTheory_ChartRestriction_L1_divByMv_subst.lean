-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divByMv_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:20:20.523045+00:00
-- url     : https://prove2.me/submissions/25c4d530-2f7f-42a5-a95f-0a3011dcebfb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_iff_divBy_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_pow
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
theorem _root_.solution {x : K} {f : PowerSeries K} {P : MvPowerSeries ι K} (hf : DivBy x f)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) : DivByMv x (f.subst P) := by
  have ha : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  intro d
  have hf' : ∀ k, ‖coeff k f‖ ≤ ‖x‖ := hf
  have hPk : ∀ k, ‖MvPowerSeries.coeff d (P ^ k)‖ ≤ 1 := fun k => by
    have h1 := (integralMv_iff_divBy_one _).mp (integralMv_pow hP k) d
    rwa [norm_one] at h1
  first
  | rw [PowerSeries.coeff_subst ha]
  | rw [PowerSeries.coeff_subst' ha]
  exact norm_finsum_le_of_forall_norm_le _ (norm_nonneg _) fun k => by
    rw [smul_eq_mul, norm_mul]
    calc ‖coeff k f‖ * ‖MvPowerSeries.coeff d (P ^ k)‖ ≤ ‖x‖ * 1 :=
          mul_le_mul (hf' k) (hPk k) (norm_nonneg _) (norm_nonneg _)
      _ = ‖x‖ := mul_one _
end ReciprocityTheory.ChartRestriction.L1

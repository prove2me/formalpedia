-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divByMv_subst2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:42:34.320079+00:00
-- url     : https://prove2.me/submissions/6ffd215c-abe4-4d2b-a13d-ba6f0cca9aaf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_iff_divBy_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_mul
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
theorem _root_.solution {x : K} {F : MvPowerSeries (Fin 2) K} {P : Fin 2 → MvPowerSeries ι K}
    (hF : DivByMv x F) (hP0 : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (hP : ∀ i, IntegralMv (P i)) : DivByMv x (F.subst P) := by
  have ha : MvPowerSeries.HasSubst P := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hP0
    | exact ⟨fun s => by rw [hP0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have hprod : ∀ e : Fin 2 →₀ ℕ, IntegralMv (e.prod fun s k => P s ^ k) := by
    intro e
    unfold Finsupp.prod
    exact Finset.prod_induction _ IntegralMv (fun _ _ => integralMv_mul) integralMv_one
      (fun s _ => integralMv_pow (hP s) _)
  intro d
  rw [MvPowerSeries.coeff_subst ha]
  exact norm_finsum_le_of_forall_norm_le _ (norm_nonneg _) fun e => by
    rw [smul_eq_mul, norm_mul]
    have h1 := (integralMv_iff_divBy_one _).mp (hprod e) d
    rw [norm_one] at h1
    calc ‖MvPowerSeries.coeff e F‖ * ‖MvPowerSeries.coeff d (e.prod fun s k => P s ^ k)‖
        ≤ ‖x‖ * 1 := mul_le_mul (hF e) h1 (norm_nonneg _) (norm_nonneg _)
      _ = ‖x‖ := mul_one _
end ReciprocityTheory.ChartRestriction.L1

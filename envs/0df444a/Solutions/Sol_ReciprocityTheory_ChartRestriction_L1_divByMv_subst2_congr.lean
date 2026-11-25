-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divByMv_subst2_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:40:39.484165+00:00
-- url     : https://prove2.me/submissions/48eb8c51-0069-4b28-b730-f8bc2903803b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_iff_divBy_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_mul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_sum
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
theorem _root_.solution {x : K} (hx : ‖x‖ ≤ 1) {F : MvPowerSeries (Fin 2) K}
    {P Q : Fin 2 → MvPowerSeries ι K} (hF : IntegralMv F)
    (hP0 : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (hQ0 : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) (hP : ∀ i, IntegralMv (P i))
    (hQ : ∀ i, IntegralMv (Q i)) (hPQ : ∀ i, DivByMv x (P i - Q i)) :
    DivByMv x (F.subst P - F.subst Q) := by
  have haP : MvPowerSeries.HasSubst P := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hP0
    | exact ⟨fun s => by rw [hP0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have haQ : MvPowerSeries.HasSubst Q := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hQ0
    | exact ⟨fun s => by rw [hQ0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have hpow : ∀ i k, DivByMv x (P i ^ k - Q i ^ k) := by
    intro i k
    rw [← geom_sum₂_mul]
    refine divByMv_mul_left ?_ (hPQ i)
    rw [integralMv_iff_divBy_one]
    exact divByMv_sum _ _ fun j _ =>
      (integralMv_iff_divBy_one _).mp (integralMv_mul (integralMv_pow (hP i) j) (integralMv_pow (hQ i) _))
  have hprod : ∀ e : Fin 2 →₀ ℕ,
      DivByMv x ((e.prod fun s k => P s ^ k) - e.prod fun s k => Q s ^ k) := by
    intro e
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fin.prod_univ_two, Fin.prod_univ_two]
    have e2 : P 0 ^ e 0 * P 1 ^ e 1 - Q 0 ^ e 0 * Q 1 ^ e 1
        = P 0 ^ e 0 * (P 1 ^ e 1 - Q 1 ^ e 1) + Q 1 ^ e 1 * (P 0 ^ e 0 - Q 0 ^ e 0) := by ring
    rw [e2]
    exact divByMv_add (divByMv_mul_left (integralMv_pow (hP 0) _) (hpow 1 _))
      (divByMv_mul_left (integralMv_pow (hQ 1) _) (hpow 0 _))
  intro d
  rw [map_sub, MvPowerSeries.coeff_subst haP, MvPowerSeries.coeff_subst haQ,
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite haP F d)
      (MvPowerSeries.coeff_subst_finite haQ F d)]
  refine norm_finsum_le_of_forall_norm_le _ (norm_nonneg _) fun e => ?_
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub, norm_mul]
  have h1 := (integralMv_iff_divBy_one F).mp hF e
  rw [norm_one] at h1
  calc ‖MvPowerSeries.coeff e F‖ *
        ‖MvPowerSeries.coeff d ((e.prod fun s k => P s ^ k) - e.prod fun s k => Q s ^ k)‖
      ≤ 1 * ‖x‖ := mul_le_mul h1 (hprod e d) (norm_nonneg _) zero_le_one
    _ = ‖x‖ := one_mul _
end ReciprocityTheory.ChartRestriction.L1

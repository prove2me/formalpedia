-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.homE_expand_subst_map_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:03:24.899414+00:00
-- url     : https://prove2.me/submissions/c28970d9-1a32-4510-a429-2bfce9eeb596

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_DivByPartialYAtZeroSubstAtXAtY
import Theorems.Thm_Formalism_LT_FrobCongr_valid
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_FrobField_funEqSetting
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_FrobField_integralMv_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_expand_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_subst_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_iff_divBy_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_pow


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
variable {lam₁ lam₂ : PowerSeries K} {Φ₁ Φ₂ : MvPowerSeries (Fin 2) K} {A₁ A₂ g : PowerSeries K}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {ι : Type} (hF : FrobField K l σ) {g₁ : PowerSeries K}
    (hg₁ : IntegralPS g₁) (hc : DivBy (l : K) (g - g₁.subst ((X : PowerSeries K) ^ l)))
    (P : MvPowerSeries ι K) (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv (l : K) (MvPowerSeries.expand l hF.prime.ne_zero (g₁.subst (MvPowerSeries.map σ P))
      - g.subst P) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  have hσ0 : MvPowerSeries.constantCoeff (MvPowerSeries.map σ P) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hP0, map_zero]
  have hs : PowerSeries.HasSubst (MvPowerSeries.map σ P) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hσ0
  have hPs : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  rw [PowerSeries.expand_subst l hl0 hs g₁]
  have hfr := Formalism.LT.FrobCongr_valid K l l hl0 σ hF.funEqSetting ι P hP
  have T1 : DivByMv (l : K) (g₁.subst (MvPowerSeries.expand l hl0 (MvPowerSeries.map σ P))
      - g₁.subst (P ^ l)) := by
    refine divByMv_subst_congr hF.norm_l.le hg₁ ?_ ?_ ?_ (integralMv_pow hP l) ?_
    · rw [MvPowerSeries.constantCoeff_expand, hσ0]
    · rw [map_pow, hP0, zero_pow hl0]
    · exact (integralMv_iff_divBy_one _).2 ((divByMv_expand_iff 1 l hl0 _).2
        ((integralMv_iff_divBy_one _).1 (hF.integralMv_map hP)))
    · rw [← neg_sub]; exact divByMv_neg hfr
  have T2 : g₁.subst (P ^ l) = PowerSeries.subst P (g₁.subst ((X : PowerSeries K) ^ l) : PowerSeries K) := by
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hl0) hPs,
      PowerSeries.subst_pow hPs, PowerSeries.subst_X hPs]
  have T3 : DivByMv (l : K) (PowerSeries.subst P (g₁.subst ((X : PowerSeries K) ^ l) : PowerSeries K) - g.subst P) := by
    rw [← PowerSeries.subst_sub hPs]
    refine divByMv_subst ?_ hP0 hP
    rw [← neg_sub]; exact divBy_neg hc
  rw [T2] at T1
  have := divByMv_add T1 T3
  rwa [sub_add_sub_cancel] at this
end ReciprocityTheory.ChartRestriction.L1

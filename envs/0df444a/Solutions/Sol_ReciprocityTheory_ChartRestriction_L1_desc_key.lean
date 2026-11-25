-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.desc_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:43:49.22828+00:00
-- url     : https://prove2.me/submissions/b797868e-96f4-49f4-9815-8b9938357f76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_desc_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_desc_congr
import Theorems.Thm_Formalism_LT_FrobCongr_valid
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_FrobField_funEqSetting
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_FrobField_integralMv_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_expand_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_iff_divBy_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_qls


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
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {ι : Type} (hF : FrobField K l σ) {D : PowerSeries K}
    (hD0 : constantCoeff D = 0) (hD' : DivBy (l : K) (derivative K D)) (P : MvPowerSeries ι K)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv (l : K) (MvPowerSeries.expand l hF.prime.ne_zero
      ((desc l D).subst (MvPowerSeries.map σ P)) - D.subst P) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  obtain ⟨h1, h2⟩ := desc_congr hF.prime hF.norm_l D hD'
  have hσP0 : MvPowerSeries.constantCoeff (MvPowerSeries.map σ P) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hP0, map_zero]
  have hPs : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  rw [PowerSeries.expand_subst l hl0 (PowerSeries.HasSubst.of_constantCoeff_zero hσP0)]
  have hfc := FrobCongr_valid K l l hl0 σ hF.funEqSetting ι P hP
  have hE0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.expand l hl0 (MvPowerSeries.map σ P)) = 0 := by
    rw [MvPowerSeries.constantCoeff_expand, hσP0]
  have hEi : IntegralMv (MvPowerSeries.expand l hl0 (MvPowerSeries.map σ P)) := by
    rw [integralMv_iff_divBy_one, divByMv_expand_iff, ← integralMv_iff_divBy_one]
    exact hF.integralMv_map hP
  have hPl0 : MvPowerSeries.constantCoeff (P ^ l) = 0 := by
    rw [map_pow, hP0, zero_pow hl0]
  have h3 := qls hF.prime hF.norm_l (desc l D) (by rw [desc_const, hD0]) h2
    (MvPowerSeries.expand l hl0 (MvPowerSeries.map σ P)) (P ^ l) hE0 hPl0 hEi
    (integralMv_pow hP l) (by
      have := divByMv_neg hfc
      rwa [neg_sub] at this)
  have h4 : (desc l D).subst (P ^ l) =
      PowerSeries.subst P ((desc l D).subst ((X : PowerSeries K) ^ l) : PowerSeries K) := by
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hl0) hPs,
      PowerSeries.subst_pow hPs, PowerSeries.subst_X hPs]
  have h5 := divByMv_subst h1 hP0 hP
  rw [PowerSeries.subst_sub hPs, ← h4] at h5
  have := divByMv_sub h3 h5
  rwa [sub_sub_sub_cancel_right] at this
end ReciprocityTheory.ChartRestriction.L1

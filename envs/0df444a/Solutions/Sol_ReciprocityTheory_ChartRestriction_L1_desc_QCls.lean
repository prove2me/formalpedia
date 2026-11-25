-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.desc_QCls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:40.285263+00:00
-- url     : https://prove2.me/submissions/075abf04-06f7-4ef2-a9bb-6c2ced3e6ae1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_desc_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_desc_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_desc_key
import Theorems.Thm_Formalism_LT_Asm_integralMv_X
import Theorems.Thm_Formalism_LT_InvIntP_Low_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_expand_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_mul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_iff_mv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_iff_mv


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
theorem _root_.solution (hF : FrobField K l σ) {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {b : K}
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) (hΦ : IntegralMv Φ) (hA0 : constantCoeff A = 0)
    (hA : IntegralPS A) (hb : ‖b‖ ≤ 1) {D : PowerSeries K} (hD : QCls l Φ A b D)
    (hD' : DivBy (l : K) (derivative K D)) :
    QCls l (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) b (desc l D) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  refine ⟨by rw [desc_const, hD.D0], (desc_congr hF.prime hF.norm_l D hD').2, ?_, ?_⟩
  · rw [← divByMv_expand_iff _ l hl0, map_sub, map_sub]
    have h1 := desc_key hF hD.D0 hD' Φ hΦ0 hΦ
    have h2 := desc_key hF hD.D0 hD' (MvPowerSeries.X (0 : Fin 2)) (by simp) (integralMv_X _)
    have h3 := desc_key hF hD.D0 hD' (MvPowerSeries.X (1 : Fin 2)) (by simp) (integralMv_X _)
    rw [MvPowerSeries.map_X] at h2 h3
    have h4 := divByMv_add (divByMv_sub (divByMv_sub h1 h2) h3) hD.add
    convert h4 using 1
    simp only [atX, atY]
    ring
  · rw [divBy_iff_mv, ← divByMv_expand_iff _ l hl0, map_sub, map_mul]
    have h1 := desc_key hF hD.D0 hD' (ι := Unit) A hA0 ((integralPS_iff_mv A).1 hA)
    have h2 := desc_key hF hD.D0 hD' (ι := Unit) (X : PowerSeries K) (by simp [PowerSeries.X])
      ((integralPS_iff_mv _).1 integralPS_X)
    rw [show MvPowerSeries.map σ (X : PowerSeries K) = (X : PowerSeries K) from PowerSeries.map_X σ,
      PowerSeries.X_subst, PowerSeries.X_subst] at h2
    have h3 := divByMv_mul_left ((integralPS_iff_mv _).1 (integralPS_C hb)) h2
    have h4 := divByMv_add (divByMv_sub h1 h3) ((divBy_iff_mv _ _).1 hD.eig)
    have hC : MvPowerSeries.expand l hl0 (C b : PowerSeries K) = (C b : PowerSeries K) :=
      PowerSeries.expand_C l hl0 b
    rw [hC]
    convert h4 using 1
    simp only [PowerSeries.map]
    ring
end ReciprocityTheory.ChartRestriction.L1

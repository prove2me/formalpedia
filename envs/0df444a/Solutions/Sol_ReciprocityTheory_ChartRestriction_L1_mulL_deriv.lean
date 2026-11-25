-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.mulL_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:59:01.846904+00:00
-- url     : https://prove2.me/submissions/4cca09da-59f5-4318-87cc-0ad2c4f2e128

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_DivByPartialYAtZeroSubstAtXAtY
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SubstOfLog
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_deriv_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_deriv_integral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_of_mul_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_subst
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
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (h : LawD lam Φ) {e : PowerSeries K} (he0 : constantCoeff e = 0)
    (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) :
    DivBy (l : K) (derivative K e) := by
  have hes : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have h1 : (derivative K lam).subst e * derivative K e = C (l : K) * derivative K lam := by
    rw [← PowerSeries.derivative_subst hes, hlog]
    simp
  have hi : IntegralPS ((derivative K lam).subst e) :=
    (integralPS_iff_mv _).2 (integralMv_subst h.deriv_integral he0 ((integralPS_iff_mv _).1 he))
  have hc : constantCoeff ((derivative K lam).subst e) = 1 := by
    rw [← h.deriv_const]
    exact Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) (τ := Unit) (derivative K lam)
      (b := fun _ => e) (fun _ => he0)
  refine divBy_of_mul_unit hi (by rw [hc, norm_one]) ?_
  rw [h1]
  intro n
  rw [coeff_C_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (h.deriv_integral n)
end ReciprocityTheory.ChartRestriction.L1

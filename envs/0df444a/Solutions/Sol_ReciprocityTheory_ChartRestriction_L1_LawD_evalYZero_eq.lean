-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.LawD.evalYZero_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:28:49.991085+00:00
-- url     : https://prove2.me/submissions/2fda5ca3-8ca4-492f-9532-2e060b0224bf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_evalYZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_evalYZero_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_evalYZero_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_evalYZero_atX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_evalYZero_atY
import Theorems.Thm_Formalism_G_LogP_evalYZero_atY


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
theorem _root_.solution (h : LawD lam Φ) : ev0 Φ = X := by
  have hc : constantCoeff (ev0 Φ) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_evalYZero, Finsupp.single_zero,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h.Φ0
  have h1 := congrArg ev0 h.log
  rw [evalYZero_subst lam h.Φ0, evalYZero_add, evalYZero_atX, evalYZero_atY, h.lam0, map_zero, add_zero] at h1
  have hu : IsUnit (coeff 1 lam) := by rw [h.lam1]; exact isUnit_one
  have hl : HasSubst lam := HasSubst.of_constantCoeff_zero h.lam0
  have he : HasSubst (ev0 Φ) := HasSubst.of_constantCoeff_zero hc
  have h2 := PowerSeries.subst_comp_subst_apply hl he (lam.substInvOfIsUnit hu)
  rw [PowerSeries.subst_substInvOfIsUnit_left lam h.lam0 hu, PowerSeries.subst_X he, h1,
    PowerSeries.subst_substInvOfIsUnit_left lam h.lam0 hu] at h2
  exact h2
end LawD
end ReciprocityTheory.ChartRestriction.L1

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.partialYAtZero_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:05:41.361169+00:00
-- url     : https://prove2.me/submissions/109359b5-70b5-41f2-b622-dd0d91559872

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_evalYZero_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_evalYZero_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_partialYAtZero_eq
import Theorems.Thm_Formalism_G_LogCR_pderiv_psubst


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
theorem _root_.solution (D : PowerSeries K) {P : MvPowerSeries (Fin 2) K}
    (hP : MvPowerSeries.constantCoeff P = 0) :
    d2 (D.subst P) = (derivative K D).subst (ev0 P) * d2 P := by
  rw [partialYAtZero_eq, Formalism.G.LogCR.pderiv_psubst hP, evalYZero_mul, evalYZero_subst _ hP, partialYAtZero_eq]
end ReciprocityTheory.ChartRestriction.L1

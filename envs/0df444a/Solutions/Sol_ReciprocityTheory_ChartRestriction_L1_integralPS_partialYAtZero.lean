-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.integralPS_partialYAtZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:37:22.964463+00:00
-- url     : https://prove2.me/submissions/7800990c-5c41-4e51-8a74-46ac9bfdf723

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB

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
theorem _root_.solution (hΦ : IntegralMv Φ) : IntegralPS (d2 Φ) := by
  unfold IntegralMv at hΦ
  unfold IntegralPS d2
  intro n
  rw [coeff_mk]
  exact hΦ _
end ReciprocityTheory.ChartRestriction.L1

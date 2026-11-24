-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divBy_partialYAtZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:56:58.121798+00:00
-- url     : https://prove2.me/submissions/7803efb8-ed87-4e82-a929-c9e5c77cdf54

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
theorem _root_.solution {x : K} {F : MvPowerSeries (Fin 2) K} (hF : DivByMv x F) : DivBy x (d2 F) := by
  unfold DivByMv at hF
  unfold DivBy d2
  intro n
  rw [coeff_mk]
  exact hF _
end ReciprocityTheory.ChartRestriction.L1

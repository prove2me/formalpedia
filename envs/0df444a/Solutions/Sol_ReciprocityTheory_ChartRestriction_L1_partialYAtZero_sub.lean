-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.partialYAtZero_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:57:08.828798+00:00
-- url     : https://prove2.me/submissions/a4fb0545-92c2-4748-beaa-08ec2f8827be

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
theorem _root_.solution (F G : MvPowerSeries (Fin 2) K) : d2 (F - G) = d2 F - d2 G := by
  ext n
  simp only [d2, PowerSeries.coeff_mk, map_sub]
end ReciprocityTheory.ChartRestriction.L1

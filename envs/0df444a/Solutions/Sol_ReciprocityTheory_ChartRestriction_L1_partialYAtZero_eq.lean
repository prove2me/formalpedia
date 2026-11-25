-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.partialYAtZero_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:45:27.601913+00:00
-- url     : https://prove2.me/submissions/562b815d-3c92-4f35-a7ee-e97428cc4def

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_evalYZero

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
theorem _root_.solution (F : MvPowerSeries (Fin 2) K) : d2 F = ev0 (MvPowerSeries.pderiv K 1 F) := by
  ext n
  rw [coeff_evalYZero, MvPowerSeries.coeff_pderiv]
  simp [d2]
end ReciprocityTheory.ChartRestriction.L1

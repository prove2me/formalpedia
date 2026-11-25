-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_L1_divBy_C_mul__2cea45c9b452
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:19:48.105536+00:00
-- url     : https://prove2.me/submissions/0abf3607-b5de-48af-a53a-0ec489c29187

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD

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
theorem _root_.solution {x c : K} (hc : ‖c‖ ≤ ‖x‖) {f : PowerSeries K} (hf : IntegralPS f) :
    DivBy x (C c * f) := by
  unfold DivBy IntegralPS at *
  intro n
  rw [coeff_C_mul, norm_mul]
  calc ‖c‖ * ‖coeff n f‖ ≤ ‖x‖ * 1 := mul_le_mul hc (hf n) (norm_nonneg _) (norm_nonneg _)
    _ = ‖x‖ := mul_one _
end ReciprocityTheory.ChartRestriction.L1

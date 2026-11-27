-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divBy_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:27:48.803836+00:00
-- url     : https://prove2.me/submissions/0ffb51a8-93e3-40c9-b712-913b8ff8d1d0

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
theorem _root_.solution {x c : K} (hc : ‖c‖ ≤ 1) {f : PowerSeries K} (hf : DivBy x f) :
    DivBy x (C c * f) := by
  unfold DivBy at *
  intro n
  rw [coeff_C_mul, norm_mul]
  calc ‖c‖ * ‖coeff n f‖ ≤ 1 * ‖x‖ := mul_le_mul hc (hf n) (norm_nonneg _) zero_le_one
    _ = ‖x‖ := one_mul _
end ReciprocityTheory.ChartRestriction.L1

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.HD.norm_a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:40:59.877432+00:00
-- url     : https://prove2.me/submissions/1b2b9b0f-ef78-4132-8c4f-3925e2394079

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_HD_coeff_one_A

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
namespace HD
theorem _root_.solution (h : HD σ lam Φ A a) : ‖a‖ ≤ 1 := by
  have h1 := h.Aint
  unfold IntegralPS at h1
  rw [← h.coeff_one_A]
  exact h1 1
end HD
end ReciprocityTheory.ChartRestriction.L1

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.QCls.norm_coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:19:14.27074+00:00
-- url     : https://prove2.me/submissions/df315b80-7a3b-4f09-a80f-e4cedc3b88bb

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
namespace QCls
theorem _root_.solution {b : K} {D : PowerSeries K} (hD : QCls l Φ A b D) :
    ‖coeff 1 D‖ ≤ 1 := by
  have h0 := hD.dInt
  unfold IntegralPS at h0
  have h1 := h0 0
  rw [coeff_derivative] at h1
  simpa using h1
end QCls
end ReciprocityTheory.ChartRestriction.L1

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.LawD.deriv_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:57:09.36472+00:00
-- url     : https://prove2.me/submissions/a8f39d1a-73d4-498f-a112-6adb80eda313

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
namespace LawD
theorem _root_.solution (h : LawD lam Φ) : constantCoeff (derivative K lam) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
  simp [h.lam1]
end LawD
end ReciprocityTheory.ChartRestriction.L1

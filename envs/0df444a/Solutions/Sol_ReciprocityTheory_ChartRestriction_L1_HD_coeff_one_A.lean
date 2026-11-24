-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.HD.coeff_one_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:29:14.040533+00:00
-- url     : https://prove2.me/submissions/9c5fd42c-721a-4dcc-9f09-a41197b3c549

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeffOne_subst_zero

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
theorem _root_.solution (h : HD σ lam Φ A a) : coeff 1 A = a := by
  have h1 := congrArg (coeff 1) h.Alog
  rw [coeffOne_subst_zero h.A0, coeff_C_mul, h.lam1, one_mul, mul_one] at h1
  exact h1
end HD
end ReciprocityTheory.ChartRestriction.L1

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.HD.qcls_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:27:33.555923+00:00
-- url     : https://prove2.me/submissions/97fdbb60-c0d4-428b-9dd0-8277200dcfc8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LawD_deriv_integral


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
theorem _root_.solution (h : HD σ lam Φ A a) : QCls l Φ A a lam := by
  refine ⟨h.lam0, h.toLawD.deriv_integral, ?_, ?_⟩
  · have h0 : lam.subst Φ - atX lam - atY lam = 0 := by rw [h.log]; ring
    rw [h0]
    unfold DivByMv
    intro e
    simp
  · have h0 : lam.subst A - C a * lam = 0 := by rw [h.Alog]; ring
    rw [h0]
    unfold DivBy
    intro n
    simp
end HD
end ReciprocityTheory.ChartRestriction.L1

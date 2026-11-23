-- Prove2me | solution 1 for PI.WGL.LTD.sz_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:23.096101+00:00
-- url     : https://prove2.me/submissions/7fcdc9ae-05ad-41d6-b520-fd27f0328052

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleD
import Theorems.Thm_PI_WGL_LTD_card_lt_sz
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTD
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC
namespace PI.WGL.LTD
theorem _root_.solution {n K : ℕ} (sg : DomWeight n) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (hshape : shapeDeg sz = sg.natW) (k : Fin K) : sz k < n ∨ sz k = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · right; have := hsz k; omega
  · left
    have h1 := card_lt_sz sg sz hshape ⟨n - 1, by omega⟩
    have h0 : sg.natW ⟨n - 1, by omega⟩ = 0 := by
      simp [DomWeight.natW, DomWeight.detShift, dif_pos hn]
    rw [h0, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
    have hk := h1 (Finset.mem_univ k)
    simp only [not_lt] at hk
    have := hsz k
    omega
end PI.WGL.LTD

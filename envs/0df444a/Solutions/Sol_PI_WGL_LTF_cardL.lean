-- Prove2me | solution 1 for PI.WGL.LTF.cardL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:08:50.138913+00:00
-- url     : https://prove2.me/submissions/f58c0fcc-8644-4691-ac40-373fcdd15257

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleF
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGL_LTD_sz_lt
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
open PI PI.WGL PI.WGL.LTF
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD PI.WGL.LTE
namespace PI.WGL.LTF
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (hshape : shapeDeg sz = sg.natW) (L : Finset (Fin K)) (hL : GoodL h lam sg sz L) :
    L.card = ∑ i : Fin n, (if i.1 = 0 then 0 else (bb h lam sg i).toNat) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := sz) (t := Finset.range n) ?_]
  · rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hL.2 i]
    congr 1
    ext k
    simp [Finset.mem_filter]
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_range]
    replace hk := Finset.mem_coe.mp hk
    rcases sz_lt sg sz hsz hshape k with h1 | h1
    · exact h1
    · exact absurd h1 (Nat.pos_iff_ne_zero.mp (hL.1 k hk))
end PI.WGL.LTF

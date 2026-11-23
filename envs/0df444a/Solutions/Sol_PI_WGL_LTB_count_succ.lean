-- Prove2me | solution 1 for PI.WGL.LTB.count_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:22.063965+00:00
-- url     : https://prove2.me/submissions/4d889d1c-a2ff-49b3-802f-0b9467a5f882

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
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
open PI PI.WGL PI.WGL.LTB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM
namespace PI.WGL.LTB
theorem _root_.solution {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (s : Fin n) :
    (Finset.univ.filter fun k => sz k = s.1 + 1).card = shapeDeg sz s - nuNext (shapeDeg sz) s := by
  unfold nuNext shapeDeg
  split_ifs with h
  · try simp only [Fin.val_mk]
    have hsub : (Finset.univ.filter fun k : Fin K => s.1 + 1 < sz k) ⊆ Finset.univ.filter fun k : Fin K => s.1 < sz k := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      omega
    first
    | rw [← Finset.card_sdiff_of_subset hsub]
    | rw [← Finset.card_sdiff hsub]
    apply congrArg Finset.card
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    omega
  · rw [Nat.sub_zero]
    apply congrArg Finset.card
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 := hsz k
    have h2 := s.2
    omega
end PI.WGL.LTB

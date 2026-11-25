-- Prove2me | solution 1 for PI.WGL.XiA.tele_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:15:46.120144+00:00
-- url     : https://prove2.me/submissions/3c95511a-e5ad-4040-883d-764ea6e3d49e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
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
open PI PI.WGL PI.WGL.XiA
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.XiA
theorem _root_.solution (ℓ : ℕ → ℤ) (n t : ℕ) (ht : t ≤ n) :
    ∑ i ∈ Finset.range n, (if t ≤ i then ℓ i - ℓ (i + 1) else 0) = ℓ t - ℓ n := by
  induction n with
  | zero =>
    have ht0 : t = 0 := by omega
    subst ht0
    simp
  | succ n ih =>
    rcases Nat.lt_or_ge n t with h | h
    · have htn : t = n + 1 := by omega
      subst htn
      rw [Finset.sum_eq_zero]
      · ring
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [if_neg (by omega)]
    · rw [Finset.sum_range_succ, ih h, if_pos h]
      ring
end PI.WGL.XiA

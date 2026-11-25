-- Prove2me | solution 1 for PI.WGL.XiB.teleA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:14:21.145631+00:00
-- url     : https://prove2.me/submissions/65a6db58-6492-445b-bed1-289c90a39e14

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
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
open PI PI.WGL PI.WGL.XiB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.XiB
theorem _root_.solution {G : Type*} [AddCommGroup G] (n : ℕ) (P : ℕ → G) (hP0 : P 0 = 0) (w : G) (ℓ σ : ℕ → ℤ) :
    ℓ n • (P n + w) + ∑ i ∈ Finset.range n, ((σ i - ℓ (i + 1)) • P (i + 1) + (ℓ i - σ i) • (P i + w)) =
    (∑ j ∈ Finset.range n, σ j • (P (j + 1) - P j)) +
      ((∑ p ∈ Finset.range (n + 1), ℓ p) - ∑ j ∈ Finset.range n, σ j) • w := by
  induction n with
  | zero => simp [hP0]
  | succ n ih =>
    rw [Finset.sum_range_succ, eq_sub_of_add_eq' ih]
    simp only [Finset.sum_range_succ]
    simp only [smul_add, smul_sub, add_smul, sub_smul]
    abel
end PI.WGL.XiB

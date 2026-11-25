-- Prove2me | solution 1 for PI.WGL.XiB.teleM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:29:37.511862+00:00
-- url     : https://prove2.me/submissions/eb323c1a-789a-4469-855f-b3989b0f9d61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
import Theorems.Thm_PI_WGL_XiB_teleA
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
theorem _root_.solution {G : Type*} [CommGroup G] (n : ℕ) (P : ℕ → G) (hP0 : P 0 = 1) (w : G) (ℓ σ : ℕ → ℤ) :
    (P n * w) ^ ℓ n * ∏ i ∈ Finset.range n, (P (i + 1) ^ (σ i - ℓ (i + 1)) * (P i * w) ^ (ℓ i - σ i)) =
    (∏ j ∈ Finset.range n, (P (j + 1) / P j) ^ σ j) *
      w ^ ((∑ p ∈ Finset.range (n + 1), ℓ p) - ∑ j ∈ Finset.range n, σ j) := by
  have h := teleA (G := Additive G) n (fun i => Additive.ofMul (P i)) (by simp [hP0])
    (Additive.ofMul w) ℓ σ
  have h2 := congrArg Additive.toMul h
  simpa [toMul_sum, toMul_zsmul, toMul_sub, toMul_add, mul_zpow] using h2
end PI.WGL.XiB

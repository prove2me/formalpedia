-- Prove2me | solution 1 for PI.WGL.XiA.initMinor_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:32.4678+00:00
-- url     : https://prove2.me/submissions/7099bb9b-9f76-4337-af53-43c02fdb54fa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Theorems.Thm_Formalism_GradedWeylDivisibility_bidetMem
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
theorem _root_.solution {N s : ℕ} (I : Fin s → Fin N) (hs : s ≤ N) :
    Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs ∈
      Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (fun t : Fin N => if t.1 < s then 1 else 0) := by
  have hm := Formalism.GradedWeylDivisibility.bidetMem ℂ N N 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have e1 : Formalism.GradedWeylDivisibility.bideterminant ℂ (r := N) (n := N) (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) =
      Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs := by
    simp [Formalism.GradedWeylDivisibility.bideterminant]
  have e2 : Formalism.GradedWeylDivisibility.shapeDeg (n := N) (fun _ : Fin 1 => s) = fun t : Fin N => if t.1 < s then 1 else 0 := by
    funext t
    by_cases ht : t.1 < s <;> simp [Formalism.GradedWeylDivisibility.shapeDeg, ht]
  rwa [e1, e2] at hm
end PI.WGL.XiA

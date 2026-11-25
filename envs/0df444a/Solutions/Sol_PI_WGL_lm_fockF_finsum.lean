-- Prove2me | solution 1 for PI.WGL.lm_fockF_finsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:35:38.692803+00:00
-- url     : https://prove2.me/submissions/aed03012-de0e-4b2c-b98d-b3d8c3aa0d28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftAsm
import Theorems.Thm_PI_WGL_lm_fockF_add
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
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution {σ ι : Type*} (s : Finset ι) (y : ι → MvPolynomial σ ℂ) (g : MvPolynomial σ ℂ)
    (h0 : ∀ i ∈ s, Formalism.REAL.fockF (y i) g = 0) : Formalism.REAL.fockF (∑ i ∈ s, y i) g = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Formalism.REAL.fockF]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, lm_fockF_add, h0 i (Finset.mem_insert_self _ _),
      ih (fun j hj => h0 j (Finset.mem_insert_of_mem hj)), add_zero]
end PI.WGL

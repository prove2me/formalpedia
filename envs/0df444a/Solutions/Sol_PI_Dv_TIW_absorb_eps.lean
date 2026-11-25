-- Prove2me | solution 1 for PI.Dv.TIW.absorb_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:12:13.592026+00:00
-- url     : https://prove2.me/submissions/4b64b909-77a2-4143-995a-c449517bf270

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TraceMemOfIntR
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_TIW_eS_central
import Theorems.Thm_PI_Dv_TIW_eS_idem
import Theorems.Thm_PI_Dv_TIW_eps_mul_epsS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv NumberField
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.TIW
theorem _root_.solution (T : GoodSet K G) (s : T.S) (Q R : Pair K G) (z : MonoidAlgebra K G) :
    eps Q * eS T s * (epsS Q * z) * (eps R * eS T s) = epsS Q * z * (eps R * eS T s) := by
  calc eps Q * eS T s * (epsS Q * z) * (eps R * eS T s)
      = eps Q * (eS T s * (epsS Q * z * eps R)) * eS T s := by simp only [mul_assoc]
    _ = eps Q * ((epsS Q * z * eps R) * eS T s) * eS T s := by rw [eS_central]
    _ = (eps Q * epsS Q) * z * eps R * (eS T s * eS T s) := by simp only [mul_assoc]
    _ = epsS Q * z * (eps R * eS T s) := by rw [eps_mul_epsS, eS_idem]; simp only [mul_assoc]
end PI.Dv.TIW

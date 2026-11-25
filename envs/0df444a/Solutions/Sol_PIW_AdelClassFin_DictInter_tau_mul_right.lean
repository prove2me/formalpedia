-- Prove2me | solution 1 for PIW.AdelClassFin.DictInter.tau_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:20:30.687573+00:00
-- url     : https://prove2.me/submissions/f13b52e5-9fd1-48c6-beb1-1ad709a3a71e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
import Theorems.Thm_PIW_AdelClassFin_DictInter_tau_tmul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
open PIW.AdelClassFin.DictInter
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PIW.AdelClassFin.DictInter
theorem _root_.solution (w : E) (b : Af F) (r : E ⊗[F] Af F) :
    tau w (((1 : E) ⊗ₜ[F] b) * r) = b * tau w r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, tau_tmul, tau_tmul, mul_smul_comm]
  | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, mul_add]
end PIW.AdelClassFin.DictInter

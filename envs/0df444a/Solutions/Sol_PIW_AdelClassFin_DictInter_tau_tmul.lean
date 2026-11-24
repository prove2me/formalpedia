-- Prove2me | solution 1 for PIW.AdelClassFin.DictInter.tau_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:32:20.612702+00:00
-- url     : https://prove2.me/submissions/49443a55-3780-42ae-b2b8-58250f5d5a71

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
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
theorem _root_.solution (w e : E) (a : Af F) : tau w (e ⊗ₜ[F] a) = Algebra.trace F E (w * e) • a := by
  first
    | simp [tau]
    | rfl
end PIW.AdelClassFin.DictInter

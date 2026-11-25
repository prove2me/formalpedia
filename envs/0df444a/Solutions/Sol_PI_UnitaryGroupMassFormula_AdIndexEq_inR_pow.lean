-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.inR_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:24.848925+00:00
-- url     : https://prove2.me/submissions/83481128-1882-41f4-977c-ac3dbd13734a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPow
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_inR_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_inR_mul
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v)
    {t : v.adicCompletion I.F} (htO : t ∈ v.adicCompletionIntegers I.F)
    (ht : α * α = incL I v t * α - 1) {x : Av I v} (hx : InR I v α x) (m : ℕ) :
    InR I v α (x ^ m) := by
  induction m with
  | zero => simpa using inR_one I v α
  | succ k ih => rw [pow_succ]; exact inR_mul I v α htO ht ih hx
end PI.UnitaryGroupMassFormula.AdIndexEq

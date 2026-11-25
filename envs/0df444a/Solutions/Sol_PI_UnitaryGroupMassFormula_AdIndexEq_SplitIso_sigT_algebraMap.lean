-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso.sigT_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:36:29.800457+00:00
-- url     : https://prove2.me/submissions/00188f95-a76d-4b9f-a0d3-79980c0e3a51

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitIso
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso
open scoped TensorProduct
variable {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
namespace PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso
theorem _root_.solution (σ : E →ₐ[F] E) (x : K) :
    sigT σ (algebraMap K (K ⊗[F] E) x) = algebraMap K (K ⊗[F] E) x := by
  simp [sigT, Algebra.TensorProduct.algebraMap_apply]
end PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso

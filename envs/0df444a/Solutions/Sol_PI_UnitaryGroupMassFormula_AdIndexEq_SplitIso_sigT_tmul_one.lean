-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso.sigT_tmul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:38.956983+00:00
-- url     : https://prove2.me/submissions/e344f5b4-440e-4751-8a8a-37a5044b3ea7

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
theorem _root_.solution (σ : E →ₐ[F] E) (a : E) : sigT (K := K) σ ((1 : K) ⊗ₜ[F] a) = (1 : K) ⊗ₜ[F] σ a := by
  simp [sigT]
end PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso

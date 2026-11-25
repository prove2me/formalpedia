-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.liftHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:54:27.016108+00:00
-- url     : https://prove2.me/submissions/c38c219c-56e4-4936-b484-efa744887947

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Assemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S
variable (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (hL : LiftU) (hJ : MatVInj) (g : Uv I v) :
    liftHom I v hL hJ g = liftFn I v hL g := rfl
end PI.UnitaryGroupMassFormula.AdIndexEq

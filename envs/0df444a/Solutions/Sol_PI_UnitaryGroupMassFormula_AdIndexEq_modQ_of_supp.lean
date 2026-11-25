-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.modQ_of_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:02:44.104809+00:00
-- url     : https://prove2.me/submissions/083ba01d-6e8c-4743-b351-b398c18d9fc1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Assemble
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_liftHom_apply

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
theorem _root_.solution (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (y : I.Gf) (hy : SuppAt I v y) :
    modQ (PI.AdIndexEq.Ksub I) y = chiV I v hC hL hJ ⟨_, hU I v y⟩ := by
  show modQ (PI.AdIndexEq.Ksub I) y = modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ ⟨_, hU I v y⟩)
  rw [liftHom_apply, ← eq_liftFn I v hL hJ ⟨_, hU I v y⟩ y rfl hy]
end PI.UnitaryGroupMassFormula.AdIndexEq

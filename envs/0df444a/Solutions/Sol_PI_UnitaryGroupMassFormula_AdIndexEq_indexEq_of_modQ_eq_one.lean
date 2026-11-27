-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.indexEq_of_modQ_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:18:23.200378+00:00
-- url     : https://prove2.me/submissions/f1ea48dd-d1cc-470b-9feb-1920a6f85266

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ModQEqOneOfMemNormalizer
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_dIdx_eq_of_modQ

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
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (hK : KComm)
    (h : ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.Gf), modQ (PI.AdIndexEq.Ksub I) x = 1) :
    PI.AdIndexEq.IndexEq := by
  unfold PI.AdIndexEq.IndexEq
  intro I x
  exact dIdx_eq_of_modQ (PI.AdIndexEq.Ksub I) (hK I) x (h I x)
end PI.UnitaryGroupMassFormula.AdIndexEq

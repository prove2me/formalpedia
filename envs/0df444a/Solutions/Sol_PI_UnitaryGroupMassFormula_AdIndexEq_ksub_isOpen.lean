-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.ksub_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:20.224471+00:00
-- url     : https://prove2.me/submissions/87da82d1-0c23-417e-9bd0-0554ebb92d2f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CommensuratedOfIsOpenIsCompact
import Theorems.Thm_PI_WAU_kset_open


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
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) : IsOpen ((PI.AdIndexEq.Ksub I : Subgroup I.Gf) : Set I.Gf) :=
  PI.WAU.kset_open I
end PI.UnitaryGroupMassFormula.AdIndexEq

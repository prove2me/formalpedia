-- Prove2me | solution 1 for PI.WAU.kset_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:43:40.404065+00:00
-- url     : https://prove2.me/submissions/032a708f-628f-46f4-acb3-55d0c2a20315

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularIndex_PairwiseDisjointCosets
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionD
import Theorems.Thm_PI_WAU_kg_one_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open Formalism.MainNotions.S MeasureTheory Matrix Pointwise
namespace PI.WAU
theorem _root_.solution (I : AutInst) : IsOpen I.Kset := by
  rw [← kg_one_eq]
  exact I.topf_open 1 le_rfl
end PI.WAU

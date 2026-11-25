-- Prove2me | solution 1 for PI.WAU.ksub_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:05:48.597908+00:00
-- url     : https://prove2.me/submissions/07a82982-63b2-4025-8d48-c4e0c43ec717

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularIndex_PairwiseDisjointCosets
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionD

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
theorem _root_.solution (I : AutInst) : ((Ksub I : Subgroup I.Gf) : Set I.Gf) = I.Kset := rfl
end PI.WAU

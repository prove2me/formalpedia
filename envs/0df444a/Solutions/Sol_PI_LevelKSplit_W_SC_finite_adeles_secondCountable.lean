-- Prove2me | solution 1 for PI.LevelKSplit.W.SC.finite_adeles_secondCountable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:47.972799+00:00
-- url     : https://prove2.me/submissions/ead84b67-9bb3-4429-ac6b-de0d1d799011

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemidirectExistsOfParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_FiniteAdelesSecondCountable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SC
namespace PI.LevelKSplit.W.SC
theorem _root_.solution : PI.LevelKSplit.W.ExS.SCAf := fun F _ _ =>
  PI.VolStabSW.TopoAF.secondCountable_finiteAdeleRing F
end PI.LevelKSplit.W.SC

-- Prove2me | solution 1 for PositivityTheory.PfBern.Loc.sb_eq_SC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:22:20.521832+00:00
-- url     : https://prove2.me/submissions/cf005c1b-36ad-4669-983c-e7361b817f51

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FiberLocalization_EqZeroOfFiberEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FiberLocalization_EqZeroOfFiberEquivariantSB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Loc
namespace PositivityTheory.PfBern.Loc
theorem _root_.solution (X : Type*) [TopologicalSpace X] : GlobalTheory.SplitWeil.SB X = SC X :=
  rfl
end PositivityTheory.PfBern.Loc

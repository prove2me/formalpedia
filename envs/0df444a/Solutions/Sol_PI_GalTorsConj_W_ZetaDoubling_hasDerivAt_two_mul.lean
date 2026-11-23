-- Prove2me | solution 1 for PI.GalTorsConj.W.ZetaDoubling.hasDerivAt_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:05.183301+00:00
-- url     : https://prove2.me/submissions/3ab5cf65-bd6b-4fa3-842d-cad2846875d4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Formalism.L2.Th1.F
open Filter Topology
open PI.GalTorsConj.W.ZetaDoubling
open OriginCoordinatesAdd
namespace PI.GalTorsConj.W.ZetaDoubling
theorem _root_.solution (z : ℂ) : HasDerivAt (fun y : ℂ => 2 * y) 2 z := by
  simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
end PI.GalTorsConj.W.ZetaDoubling

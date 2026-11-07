-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.primalMembraneSweepPath_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:27:37.922734+00:00
-- url     : https://prove2.me/submissions/30b474a4-7bec-4659-8676-d58cca1d4c2e

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution (z w : ZMod L) :
    (primalMembraneSweepPath z w).endpoint =
      primalMembraneError (primalXYMembrane z w) := by
  exact PauliErrorPath.orderedExact_endpoint _ _ _ _
end QEC.Coding.PeriodicCubical4

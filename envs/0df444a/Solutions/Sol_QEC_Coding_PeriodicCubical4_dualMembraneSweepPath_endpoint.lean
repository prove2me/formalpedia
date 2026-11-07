-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.dualMembraneSweepPath_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:27:30.045212+00:00
-- url     : https://prove2.me/submissions/b9c50a23-3135-48d5-b121-8652610c6b87

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
theorem _root_.solution (x y : ZMod L) :
    (dualMembraneSweepPath x y).endpoint =
      dualMembraneError (dualXYMembrane x y) := by
  exact PauliErrorPath.orderedExact_endpoint _ _ _ _
end QEC.Coding.PeriodicCubical4

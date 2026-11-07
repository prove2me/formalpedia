-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.framePath_increments
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:21:53.756742+00:00
-- url     : https://prove2.me/submissions/f2f50830-e893-4c68-a769-af4462ba323c

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution {L : Nat} [NeZero L]
    (p : Plane) (gamma : PauliErrorPath (ι := Plaquette L)) :
    (framePath p gamma).increments = gamma.increments.map (frameBinary p) := rfl
end QEC.Coding.PeriodicCubical4

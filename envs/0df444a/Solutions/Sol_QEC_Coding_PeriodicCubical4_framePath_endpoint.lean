-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.framePath_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:11:39.976551+00:00
-- url     : https://prove2.me/submissions/8736c78e-f797-4473-b76a-a1cd4ad00d0b

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
import Theorems.Thm_QEC_Coding_PeriodicCubical4_accumulate_frameBinary

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution {L : Nat} [NeZero L]
    (p : Plane) (gamma : PauliErrorPath (ι := Plaquette L)) :
    (framePath p gamma).endpoint = frameBinary p gamma.endpoint := by
  exact accumulate_frameBinary p gamma.increments
end QEC.Coding.PeriodicCubical4

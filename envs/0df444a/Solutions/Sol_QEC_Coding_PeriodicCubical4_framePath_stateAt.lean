-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.framePath_stateAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:11:44.475941+00:00
-- url     : https://prove2.me/submissions/8a38165a-c998-440b-89f7-743572be4d37

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
    (p : Plane) (gamma : PauliErrorPath (ι := Plaquette L)) (n : Nat) :
    (framePath p gamma).stateAt n = frameBinary p (gamma.stateAt n) := by
  change PauliErrorPath.accumulate
      ((gamma.increments.map (frameBinary p)).take n) =
    frameBinary p (PauliErrorPath.accumulate (gamma.increments.take n))
  rw [← List.map_take]
  exact accumulate_frameBinary p (gamma.increments.take n)
end QEC.Coding.PeriodicCubical4

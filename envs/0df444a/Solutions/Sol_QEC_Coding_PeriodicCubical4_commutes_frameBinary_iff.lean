-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.commutes_frameBinary_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:04:55.327602+00:00
-- url     : https://prove2.me/submissions/19945b03-af31-4fdc-a424-674055aa6609

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
import Theorems.Thm_QEC_Coding_PeriodicCubical4_symplecticForm_frameBinary

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution {L : Nat} [NeZero L]
    (p : Plane) (E F : Binary (Plaquette L)) :
    Commutes (frameBinary p E) (frameBinary p F) ↔ Commutes E F := by
  change
    symplecticForm (frameBinary p E).vector (frameBinary p F).vector = 0 ↔
      symplecticForm E.vector F.vector = 0
  rw [symplecticForm_frameBinary]
end QEC.Coding.PeriodicCubical4

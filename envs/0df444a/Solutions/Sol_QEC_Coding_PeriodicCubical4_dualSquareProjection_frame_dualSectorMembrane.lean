-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.dualSquareProjection_frame_dualSectorMembrane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:26:55.447823+00:00
-- url     : https://prove2.me/submissions/69f06fa9-10bc-4aa8-ae5f-27c0be510443

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
import Theorems.Thm_QEC_Coding_PeriodicCubical4_wordPairing_framePlaquetteWord_left
import Theorems.Thm_QEC_Coding_PeriodicCubical4_dualSectorMembrane_pairing

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (s : MembraneSector) (p : Plane) (hp : p ∈ s.1) :
    dualSquareProjection (framePlaquetteWord p (dualSectorMembrane s)) =
      (fun _ _ => 1 : BinarySquare.Grid L) := by
  funext w z
  rw [dualSquareProjection, wordPairing_framePlaquetteWord_left]
  exact dualSectorMembrane_pairing s p hp _ _
end QEC.Coding.PeriodicCubical4

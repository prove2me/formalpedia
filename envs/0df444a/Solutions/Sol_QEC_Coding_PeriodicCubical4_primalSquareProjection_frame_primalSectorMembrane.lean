-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.primalSquareProjection_frame_primalSectorMembrane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:29:49.567203+00:00
-- url     : https://prove2.me/submissions/175d37fe-dfdc-4c90-a3eb-27461582cc57

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
import Theorems.Thm_QEC_Coding_PeriodicCubical4_wordPairing_framePlaquetteWord_left
import Theorems.Thm_QEC_Coding_PeriodicCubical4_primalSectorMembrane_pairing
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    primalSquareProjection (framePlaquetteWord p (primalSectorMembrane s)) =
      (fun _ _ => 1 : BinarySquare.Grid L) := by
  funext y x
  rw [primalSquareProjection]
  rw [show wordPairing (dualXYMembrane (finToPeriodic x) (finToPeriodic y))
        (framePlaquetteWord p (primalSectorMembrane s)) =
      wordPairing
        (framePlaquetteWord p
          (dualXYMembrane (finToPeriodic x) (finToPeriodic y)))
        (primalSectorMembrane s) by
    exact (wordPairing_framePlaquetteWord_left p _ _).symm]
  exact primalSectorMembrane_pairing s p hp _ _
end QEC.Coding.PeriodicCubical4

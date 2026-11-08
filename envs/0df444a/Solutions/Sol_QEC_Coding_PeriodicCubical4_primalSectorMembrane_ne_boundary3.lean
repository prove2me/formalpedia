-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.primalSectorMembrane_ne_boundary3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:37:00.730997+00:00
-- url     : https://prove2.me/submissions/12999949-d163-4f0b-8810-9bceeee1a424

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
import Theorems.Thm_QEC_Coding_PeriodicCubical4_primalSectorMembrane_pairing
import Theorems.Thm_QEC_Coding_PeriodicCubical4_wordPairing_dualCoordinate_boundary3_zero

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution
    {L : Nat} [NeZero L] (s : MembraneSector)
    (c : Word (ZMod 2) (Cube L)) :
    primalSectorMembrane s ≠ boundary3 c := by
  obtain ⟨p, hp⟩ := s.2
  intro h
  have hpair := congrArg
    (fun m => wordPairing (dualCoordinateMembrane p 0 0) m) h
  change wordPairing (dualCoordinateMembrane p 0 0)
      (primalSectorMembrane s) =
    wordPairing (dualCoordinateMembrane p 0 0) (boundary3 c) at hpair
  rw [primalSectorMembrane_pairing s p hp,
    wordPairing_dualCoordinate_boundary3_zero] at hpair
  exact one_ne_zero hpair
end QEC.Coding.PeriodicCubical4

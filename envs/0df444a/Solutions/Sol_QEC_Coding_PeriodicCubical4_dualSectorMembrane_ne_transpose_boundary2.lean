-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.dualSectorMembrane_ne_transpose_boundary2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:37:31.165694+00:00
-- url     : https://prove2.me/submissions/7eb0a610-4cf0-416e-bf37-17d86d0b6693

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
import Theorems.Thm_QEC_Coding_PeriodicCubical4_dualSectorMembrane_pairing
import Theorems.Thm_QEC_Coding_PeriodicCubical4_wordPairing_transpose_boundary2_primalCoordinate_zero

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution
    {L : Nat} [NeZero L] (s : MembraneSector)
    (e : Word (ZMod 2) (Link L)) :
    dualSectorMembrane s ≠ wordLinearMapTranspose boundary2 e := by
  obtain ⟨p, hp⟩ := s.2
  intro h
  have hpair := congrArg
    (fun m => wordPairing m (primalCoordinateMembrane p 0 0)) h
  change wordPairing (dualSectorMembrane s)
      (primalCoordinateMembrane p 0 0) =
    wordPairing (wordLinearMapTranspose boundary2 e)
      (primalCoordinateMembrane p 0 0) at hpair
  rw [dualSectorMembrane_pairing s p hp,
    wordPairing_transpose_boundary2_primalCoordinate_zero] at hpair
  exact one_ne_zero hpair
end QEC.Coding.PeriodicCubical4

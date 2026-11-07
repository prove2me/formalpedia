-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.pathHeight_primalCoordinateSweepPath_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:29:35.023767+00:00
-- url     : https://prove2.me/submissions/db8aa9b0-851d-4883-b3a5-015392a73d55

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
import Theorems.Thm_QEC_Coding_PeriodicCubical4_pathHeight_framePath
import Theorems.Thm_QEC_Coding_PeriodicCubical4_pathHeight_primalMembraneSweepPath_le


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution
    {L : Nat} [NeZero L] [Fact (1 < L)] (p : Plane) :
    (toricHamiltonian (L := L)).pathHeight
      (primalCoordinateSweepPath (L := L) p) ≤ 64 * L := by
  rw [primalCoordinateSweepPath, pathHeight_framePath]
  exact pathHeight_primalMembraneSweepPath_le 0 0
end QEC.Coding.PeriodicCubical4

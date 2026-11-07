-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.half_le_pathHeight_of_hasPrimalSectorEndpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:35:50.409477+00:00
-- url     : https://prove2.me/submissions/f55b53d1-919a-4b36-af91-00457a97e90d

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
import Theorems.Thm_QEC_Coding_PeriodicCubical4_pathHeight_framePath
import Theorems.Thm_QEC_Coding_PeriodicCubical4_primalProjectionEndpoint_of_hasPrimalSectorEndpoint
import Theorems.Thm_QEC_Coding_PeriodicCubical4_half_le_pathHeight_of_primalProjectionEndpoint

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (gamma : PauliErrorPath (ι := Plaquette L)) (s : MembraneSector)
    (hendpoint : HasPrimalSectorEndpoint gamma s) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight gamma := by
  obtain ⟨p, hp⟩ := s.2
  rw [← pathHeight_framePath p gamma]
  exact half_le_pathHeight_of_primalProjectionEndpoint (framePath p gamma)
    (primalProjectionEndpoint_of_hasPrimalSectorEndpoint gamma s p hp hendpoint)
end QEC.Coding.PeriodicCubical4

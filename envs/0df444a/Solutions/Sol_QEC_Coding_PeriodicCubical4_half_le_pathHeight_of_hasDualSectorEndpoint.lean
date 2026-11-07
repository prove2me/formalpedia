-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.half_le_pathHeight_of_hasDualSectorEndpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:34:38.158964+00:00
-- url     : https://prove2.me/submissions/775cf274-adfb-4398-9f54-6a059f55a3eb

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
import Theorems.Thm_QEC_Coding_PeriodicCubical4_pathHeight_framePath
import Theorems.Thm_QEC_Coding_PeriodicCubical4_dualProjectionEndpoint_of_hasDualSectorEndpoint
import Theorems.Thm_QEC_Coding_PeriodicCubical4_half_le_pathHeight_of_dualProjectionEndpoint

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
    (hendpoint : HasDualSectorEndpoint gamma s) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight gamma := by
  obtain ⟨p, hp⟩ := s.2
  rw [← pathHeight_framePath p gamma]
  exact half_le_pathHeight_of_dualProjectionEndpoint (framePath p gamma)
    (dualProjectionEndpoint_of_hasDualSectorEndpoint gamma s p hp hendpoint)
end QEC.Coding.PeriodicCubical4

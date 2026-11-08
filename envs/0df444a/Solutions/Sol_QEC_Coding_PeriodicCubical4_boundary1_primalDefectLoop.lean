-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.boundary1_primalDefectLoop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:34:42.025921+00:00
-- url     : https://prove2.me/submissions/6e1021dc-0046-44cb-aa7b-4f0c08d7a912

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Theorems.Thm_QEC_Coding_PeriodicCubical4_boundary1_comp_boundary2


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution (m : PartialPrimalMembrane (L := L)) :
    boundary1 (primalDefectLoop m) = 0 := by
  change ((boundary1 (L := L)).comp boundary2) m = 0
  rw [boundary1_comp_boundary2]
  rfl
end QEC.Coding.PeriodicCubical4

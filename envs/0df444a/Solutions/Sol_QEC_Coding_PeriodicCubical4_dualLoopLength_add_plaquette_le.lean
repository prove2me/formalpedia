-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.dualLoopLength_add_plaquette_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:35:34.041479+00:00
-- url     : https://prove2.me/submissions/4bf7d173-0537-49d2-b571-a8754904c39c

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Theorems.Thm_QEC_Coding_PeriodicCubical4_HammingWeight_transpose_boundary3_cellWord_le_four
import Theorems.Thm_QEC_Coding_PeriodicCubical4_dualDefectLoop_add_plaquette
import Theorems.Thm_QEC_Coding_HammingWeight_add_le


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution
    (m : PartialDualMembrane (L := L)) (p : Plaquette L) :
    dualLoopLength (m + cellWord p) ≤ dualLoopLength m + 4 := by
  rw [dualLoopLength, dualDefectLoop_add_plaquette, dualLoopLength]
  exact le_trans
    (HammingWeight_add_le (dualDefectLoop m)
      (wordLinearMapTranspose boundary3 (cellWord p)))
    (Nat.add_le_add_left
      (HammingWeight_transpose_boundary3_cellWord_le_four p) _)
end QEC.Coding.PeriodicCubical4

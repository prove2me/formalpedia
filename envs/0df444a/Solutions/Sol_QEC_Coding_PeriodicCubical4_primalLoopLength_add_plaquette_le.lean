-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.primalLoopLength_add_plaquette_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:35:32.602038+00:00
-- url     : https://prove2.me/submissions/50d4c840-3a54-4f32-aed9-e90d075215d7

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Theorems.Thm_QEC_Coding_PeriodicCubical4_HammingWeight_plaquetteBoundary_le_four
import Theorems.Thm_QEC_Coding_PeriodicCubical4_primalDefectLoop_add_plaquette
import Theorems.Thm_QEC_Coding_HammingWeight_add_le


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution
    (m : PartialPrimalMembrane (L := L)) (p : Plaquette L) :
    primalLoopLength (m + cellWord p) ≤ primalLoopLength m + 4 := by
  rw [primalLoopLength, primalDefectLoop_add_plaquette, primalLoopLength]
  exact le_trans
    (HammingWeight_add_le (primalDefectLoop m) (plaquetteBoundary p))
    (Nat.add_le_add_left (HammingWeight_plaquetteBoundary_le_four p) _)
end QEC.Coding.PeriodicCubical4

-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.btExcessEnergy_primalMembrane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:56:14.188348+00:00
-- url     : https://prove2.me/submissions/a6de7ce4-2ecd-4204-b6bb-0a6a329c4b0b

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Theorems.Thm_QEC_Coding_PeriodicCubical4_unitDefectEnergy_primalMembrane
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_eq_two_mul_unitDefectEnergy


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution (m : PartialPrimalMembrane (L := L)) :
    (toricHamiltonian (L := L)).btExcessEnergy (primalMembraneError m) =
      2 * primalLoopLength m := by
  rw [btExcessEnergy_eq_two_mul_unitDefectEnergy,
    unitDefectEnergy_primalMembrane]
end QEC.Coding.PeriodicCubical4

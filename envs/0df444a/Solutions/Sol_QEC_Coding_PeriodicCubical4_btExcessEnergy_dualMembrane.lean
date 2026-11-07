-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.btExcessEnergy_dualMembrane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:56:15.649204+00:00
-- url     : https://prove2.me/submissions/cad34d81-f264-40d7-b9c8-cae331342bea

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Theorems.Thm_QEC_Coding_PeriodicCubical4_unitDefectEnergy_dualMembrane
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_eq_two_mul_unitDefectEnergy


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution (m : PartialDualMembrane (L := L)) :
    (toricHamiltonian (L := L)).btExcessEnergy (dualMembraneError m) =
      2 * dualLoopLength m := by
  rw [btExcessEnergy_eq_two_mul_unitDefectEnergy,
    unitDefectEnergy_dualMembrane]
end QEC.Coding.PeriodicCubical4

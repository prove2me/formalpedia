-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.half_le_pathHeight_of_hasDualMembraneEndpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:29:11.221913+00:00
-- url     : https://prove2.me/submissions/78675c10-2c40-4cbf-a2aa-6f11eea7260d

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Theorems.Thm_QEC_Coding_PeriodicCubical4_two_mul_dualLoopLength_le_btExcessEnergy
import Theorems.Thm_QEC_Coding_PeriodicCubical4_exists_dual_large_defect_loop
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_stateAt_le_pathHeight
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasDualMembraneEndpoint γ) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight γ := by
  obtain ⟨n, hn, hloop⟩ := exists_dual_large_defect_loop γ hendpoint
  exact hloop.trans ((two_mul_dualLoopLength_le_btExcessEnergy
    (γ.stateAt n)).trans
      ((toricHamiltonian (L := L)).btExcessEnergy_stateAt_le_pathHeight
        γ n hn))
end QEC.Coding.PeriodicCubical4

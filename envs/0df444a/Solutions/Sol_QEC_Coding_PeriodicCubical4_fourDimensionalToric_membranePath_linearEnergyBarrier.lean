-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.fourDimensionalToric_membranePath_linearEnergyBarrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:36:37.713119+00:00
-- url     : https://prove2.me/submissions/00826a34-72ad-4487-8118-4766347ab240

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Theorems.Thm_QEC_Coding_PeriodicCubical4_half_le_pathHeight_of_hasPrimalMembraneEndpoint
import Theorems.Thm_QEC_Coding_PeriodicCubical4_half_le_pathHeight_of_hasDualMembraneEndpoint

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution
    (γ : PauliErrorPath (ι := Plaquette L))
    (hendpoint : HasPrimalMembraneEndpoint γ ∨ HasDualMembraneEndpoint γ) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight γ := by
  rcases hendpoint with hprimal | hdual
  · exact half_le_pathHeight_of_hasPrimalMembraneEndpoint γ hprimal
  · exact half_le_pathHeight_of_hasDualMembraneEndpoint γ hdual
end QEC.Coding.PeriodicCubical4

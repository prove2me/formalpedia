-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.primalFullRowCount_dist_succ_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:03:19.721117+00:00
-- url     : https://prove2.me/submissions/75270025-8f8a-4060-b648-747c6e99441d

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Theorems.Thm_QEC_Coding_PeriodicCubical4_BinarySquare_fullRows_card_dist_le_one_of_oneCellStep
import Theorems.Thm_QEC_Coding_PeriodicCubical4_oneCellStep_primalSquareProjection_stateAt_succ

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution
    (γ : PauliErrorPath (ι := Plaquette L)) (n : Nat)
    (hn : n < γ.increments.length) :
    Nat.dist (primalFullRowCount γ (n + 1))
      (primalFullRowCount γ n) ≤ 1 := by
  exact BinarySquare.fullRows_card_dist_le_one_of_oneCellStep _ _
    (oneCellStep_primalSquareProjection_stateAt_succ γ n hn)
end QEC.Coding.PeriodicCubical4

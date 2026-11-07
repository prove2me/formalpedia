-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.oneCellStep_dualSquareProjection_stateAt_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:08:27.422543+00:00
-- url     : https://prove2.me/submissions/1a589232-b4c0-4fe0-91df-e303b41b3b23

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Theorems.Thm_QEC_Coding_PeriodicCubical4_oneCellStep_dualSquareProjection_of_HammingWeight_le_one
import Theorems.Thm_QEC_Coding_PeriodicCubical4_dualSquareProjection_add
import Theorems.Thm_QEC_Coding_PauliErrorPath_getElem_weight_le_one
import Theorems.Thm_QEC_Coding_PauliErrorPath_stateAt_succ
import Theorems.Thm_QEC_Coding_PauliSymplectic_hammingWeight_xPart_le_weight
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

section
noncomputable section
namespace QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
namespace BinarySquare
end BinarySquare
variable {L : Nat} [NeZero L] [Fact (1 < L)]
private theorem oneCellStep_add_self_of_oneCellStep_zero
    (g d : BinarySquare.Grid L) (h : BinarySquare.OneCellStep d 0) :
    BinarySquare.OneCellStep (g + d) g := by
  unfold BinarySquare.OneCellStep BinarySquare.difference at h ⊢
  have heq :
      (fun p : Fin L × Fin L =>
        (g + d) p.1 p.2 + g p.1 p.2) =
      (fun p : Fin L × Fin L => d p.1 p.2 + 0) := by
    funext p
    change (g p.1 p.2 + d p.1 p.2) + g p.1 p.2 = d p.1 p.2 + 0
    calc
      (g p.1 p.2 + d p.1 p.2) + g p.1 p.2 =
          d p.1 p.2 + (g p.1 p.2 + g p.1 p.2) := by ac_rfl
      _ = d p.1 p.2 + 0 := by rw [ZModModule.add_self]
  rw [heq]
  exact h
end QEC.Coding.PeriodicCubical4
end
end

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
    BinarySquare.OneCellStep
      (dualSquareProjection (γ.stateAt (n + 1)).vector.xPart)
      (dualSquareProjection (γ.stateAt n).vector.xPart) := by
  have hcomponent :
      HammingWeight γ.increments[n].vector.xPart ≤ 1 :=
    (hammingWeight_xPart_le_weight γ.increments[n]).trans
      (γ.getElem_weight_le_one n hn)
  have hlocal := oneCellStep_dualSquareProjection_of_HammingWeight_le_one
    γ.increments[n].vector.xPart hcomponent
  rw [γ.stateAt_succ n hn]
  change BinarySquare.OneCellStep
    (dualSquareProjection
      ((γ.stateAt n).vector.xPart + γ.increments[n].vector.xPart))
    (dualSquareProjection (γ.stateAt n).vector.xPart)
  rw [dualSquareProjection_add]
  exact oneCellStep_add_self_of_oneCellStep_zero _ _ hlocal
end QEC.Coding.PeriodicCubical4

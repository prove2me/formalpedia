-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.oneCellStep_primalSquareProjection_stateAt_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:00:08.915711+00:00
-- url     : https://prove2.me/submissions/8f7d2084-a614-4995-af67-66bef681276d

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Theorems.Thm_QEC_Coding_PeriodicCubical4_oneCellStep_primalSquareProjection_of_HammingWeight_le_one
import Theorems.Thm_QEC_Coding_PeriodicCubical4_primalSquareProjection_add
import Theorems.Thm_QEC_Coding_PauliErrorPath_getElem_weight_le_one
import Theorems.Thm_QEC_Coding_PauliErrorPath_stateAt_succ
import Theorems.Thm_QEC_Coding_PauliSymplectic_hammingWeight_zPart_le_weight
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
      (primalSquareProjection (γ.stateAt (n + 1)).vector.zPart)
      (primalSquareProjection (γ.stateAt n).vector.zPart) := by
  have hcomponent :
      HammingWeight γ.increments[n].vector.zPart ≤ 1 :=
    (hammingWeight_zPart_le_weight γ.increments[n]).trans
      (γ.getElem_weight_le_one n hn)
  have hlocal := oneCellStep_primalSquareProjection_of_HammingWeight_le_one
    γ.increments[n].vector.zPart hcomponent
  rw [γ.stateAt_succ n hn]
  change BinarySquare.OneCellStep
    (primalSquareProjection
      ((γ.stateAt n).vector.zPart + γ.increments[n].vector.zPart))
    (primalSquareProjection (γ.stateAt n).vector.zPart)
  rw [primalSquareProjection_add]
  exact oneCellStep_add_self_of_oneCellStep_zero _ _ hlocal
end QEC.Coding.PeriodicCubical4

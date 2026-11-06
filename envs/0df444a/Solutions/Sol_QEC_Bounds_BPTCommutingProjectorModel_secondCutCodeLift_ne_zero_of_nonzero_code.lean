-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCutCodeLift_ne_zero_of_nonzero_code
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:13:07.901891+00:00
-- url     : https://prove2.me/submissions/0e20b45d-e997-436f-9b61-5d8e757084d1

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Projection
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_LeftProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutGlobalCoordinateTransport_conj_fullCodeProjector
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥) :
    M.secondCutCodeLift region ≠ 0 := by
  have hfullNonzero : M.fullCodeProjector ≠ 0 := by
    intro hzero
    apply hcode
    apply le_antisymm
    · intro vector hvector
      have hfixed : M.fullCodeProjector vector = vector :=
        M.codeSpace.projector_eq_self_of_mem hvector
      rw [hzero] at hfixed
      simpa using hfixed.symm
    · exact bot_le
  intro hzero
  apply hfullNonzero
  calc
    M.fullCodeProjector =
        (M.secondCutGlobalCoordinateTransport region).symm.conjOperator
          ((M.secondCutGlobalCoordinateTransport region).conjOperator
            M.fullCodeProjector) :=
      (M.secondCutGlobalCoordinateTransport region).symm_conjOperator_conjOperator _ |>.symm
    _ = (M.secondCutGlobalCoordinateTransport region).symm.conjOperator
          (M.secondCutCodeLift region) := by
      rw [M.secondCutGlobalCoordinateTransport_conj_fullCodeProjector]
    _ = (M.secondCutGlobalCoordinateTransport region).symm.conjOperator 0 :=
      congrArg (M.secondCutGlobalCoordinateTransport region).symm.conjOperator hzero
    _ = 0 := by simp [Semantics.UnitaryTransport.conjOperator]

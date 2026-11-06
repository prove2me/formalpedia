-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCutCodeLift_ne_zero_of_nonzero_code
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:16:40.537077+00:00
-- url     : https://prove2.me/submissions/4a077156-d483-4f40-ad7b-a31530a35cf0

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutLeftProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutCodeNonzero
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutGlobalCoordinateTransport_conj_fullCodeProjector
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
    M.firstCutCodeLift region ≠ 0 := by
  have hfull : M.fullCodeProjector ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcode
    intro hzero
    have hxfix : M.fullCodeProjector x = x := M.codeSpace.projector_eq_self_of_mem hx
    exact hx0 (by simpa [hzero] using hxfix.symm)
  rw [← M.firstCutGlobalCoordinateTransport_conj_fullCodeProjector region]
  intro hzero
  apply hfull
  calc
    M.fullCodeProjector =
        (M.firstCutGlobalCoordinateTransport region).symm.conjOperator
          ((M.firstCutGlobalCoordinateTransport region).conjOperator M.fullCodeProjector) :=
      ((M.firstCutGlobalCoordinateTransport region).symm_conjOperator_conjOperator
        M.fullCodeProjector).symm
    _ = (M.firstCutGlobalCoordinateTransport region).symm.conjOperator 0 :=
      congrArg _ hzero
    _ = 0 := by
      ext x
      simp [Semantics.UnitaryTransport.conjOperator]

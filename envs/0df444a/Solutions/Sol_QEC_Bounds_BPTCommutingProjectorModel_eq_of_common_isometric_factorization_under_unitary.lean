-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.eq_of_common_isometric_factorization_under_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-18T04:17:07.468798+00:00
-- url     : https://prove2.me/submissions/271f7716-287e-4f69-bfc5-c538174baa42

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_eq_of_common_isometric_factorization

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {S H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (F : Semantics.UnitaryTransport H K)
    (A B : Semantics.Operator H) (P : Semantics.Operator S)
    (Eout Eleft : S →ₗ[Complex] K)
    (hA : F.conjOperator A = Eout.comp (P.comp (LinearMap.adjoint Eout)))
    (hE : Eleft = Eout)
    (hB : F.conjOperator B = Eleft.comp (P.comp (LinearMap.adjoint Eleft))) :
    A = B := by
  have hConj : F.conjOperator A = F.conjOperator B :=
    eq_of_common_isometric_factorization
      (F.conjOperator A) (F.conjOperator B) P Eout Eleft hA hE hB
  calc
    A = F.symm.conjOperator (F.conjOperator A) :=
      (F.symm_conjOperator_conjOperator _).symm
    _ = F.symm.conjOperator (F.conjOperator B) := congrArg F.symm.conjOperator hConj
    _ = B := F.symm_conjOperator_conjOperator _
end QEC.Bounds.BPTCommutingProjectorModel

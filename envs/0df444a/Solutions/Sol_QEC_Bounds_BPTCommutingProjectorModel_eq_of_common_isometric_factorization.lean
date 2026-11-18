-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.eq_of_common_isometric_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-18T04:13:26.880977+00:00
-- url     : https://prove2.me/submissions/99430e1d-14e0-4001-8c6b-3d19475410d6

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers

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
    {S H : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (A B : Semantics.Operator H) (P : Semantics.Operator S)
    (Eout Eleft : S →ₗ[Complex] H)
    (hA : A = Eout.comp (P.comp (LinearMap.adjoint Eout)))
    (hE : Eleft = Eout)
    (hB : B = Eleft.comp (P.comp (LinearMap.adjoint Eleft))) :
    A = B := by
  calc
    A = Eout.comp (P.comp (LinearMap.adjoint Eout)) := hA
    _ = Eleft.comp (P.comp (LinearMap.adjoint Eleft)) := by rw [hE]
    _ = B := hB.symm
end QEC.Bounds.BPTCommutingProjectorModel

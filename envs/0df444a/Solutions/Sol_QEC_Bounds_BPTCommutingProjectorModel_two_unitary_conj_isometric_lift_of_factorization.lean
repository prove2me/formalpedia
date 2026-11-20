-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.two_unitary_conj_isometric_lift_of_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:12:13.937514+00:00
-- url     : https://prove2.me/submissions/f7d4f512-0df5-4a91-bdb0-6fb21b2a0be6

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryTransport_conj_isometric_lift

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
    {S H K R : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup R] [InnerProductSpace Complex R] [Semantics.FiniteQuantumSystem R]
    (Tinner : Semantics.UnitaryTransport H K)
    (Touter : Semantics.UnitaryTransport K R)
    (J : S →ₗ[Complex] H) (P : Semantics.Operator S)
    (Q : Semantics.Operator H)
    (E : S →ₗ[Complex] R)
    (hQ : Q = J.comp (P.comp (LinearMap.adjoint J)))
    (hE : Touter.toLinearEquiv.toLinearMap.comp
        (Tinner.toLinearEquiv.toLinearMap.comp J) = E) :
    Touter.conjOperator (Tinner.conjOperator Q) =
      E.comp (P.comp (LinearMap.adjoint E)) := by
  rw [hQ]
  rw [unitaryTransport_conj_isometric_lift Tinner J P]
  rw [unitaryTransport_conj_isometric_lift Touter
    (Tinner.toLinearEquiv.toLinearMap.comp J) P]
  rw [hE]
end QEC.Bounds.BPTCommutingProjectorModel

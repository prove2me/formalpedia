-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isometricCompression_left_support_of_right_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:52:16.655004+00:00
-- url     : https://prove2.me/submissions/bff43ef8-2aca-4c32-80ec-d3dcbd7df1d7

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Factorization
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ActiveProjection

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (Jadj : K →ₗ[Complex] H)
    (Q : Semantics.Operator K)
    (hJadj_eq : LinearMap.adjoint J = Jadj)
    (hQ : Q.IsSymmetricProjection)
    (hright : Q.comp (J.comp Jadj) = Q) :
    (J.comp Jadj).comp Q = Q := by
  have hJadjadj : LinearMap.adjoint Jadj = J := by
    calc
      LinearMap.adjoint Jadj = LinearMap.adjoint (LinearMap.adjoint J) := by
        rw [hJadj_eq]
      _ = J := LinearMap.adjoint_adjoint J
  have hSself : LinearMap.adjoint (J.comp Jadj) = J.comp Jadj := by
    rw [LinearMap.adjoint_comp, hJadjadj, hJadj_eq]
  have hQself : LinearMap.adjoint Q = Q := hQ.isSymmetric.adjoint_eq
  calc
    (J.comp Jadj).comp Q = LinearMap.adjoint (Q.comp (J.comp Jadj)) := by
      rw [LinearMap.adjoint_comp, hSself, hQself]
    _ = LinearMap.adjoint Q := congrArg LinearMap.adjoint hright
    _ = Q := hQself
end QEC.Bounds.BPTCommutingProjectorModel

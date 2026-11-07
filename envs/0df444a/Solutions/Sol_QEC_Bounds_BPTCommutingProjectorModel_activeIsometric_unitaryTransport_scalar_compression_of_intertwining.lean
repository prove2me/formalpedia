-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.activeIsometric_unitaryTransport_scalar_compression_of_intertwining
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:18:48.873889+00:00
-- url     : https://prove2.me/submissions/a8d377fd-bc93-4acc-a6fb-f4ee194a858a

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Data
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Core
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryTransport_conj_scalar_compression
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isometricCompression_left_support_of_right_support
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isometricCompression_scalar_of_intertwining


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
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {H K K' : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup K'] [InnerProductSpace Complex K']
    [Semantics.FiniteQuantumSystem K']
    (J : H →ₗ[Complex] K) (Jadj : K →ₗ[Complex] H)
    (Q R : Semantics.Operator K) (Rsub : Semantics.Operator H)
    (T : Semantics.UnitaryTransport H K') (scalar : Complex)
    (hJadj_eq : LinearMap.adjoint J = Jadj)
    (hQ : Q.IsSymmetricProjection)
    (hright : Q.comp (J.comp Jadj) = Q)
    (hscalar : Q * R * Q = scalar • Q)
    (hintertwines : J.comp Rsub = R.comp J) :
    T.conjOperator (Jadj.comp (Q.comp J)) * T.conjOperator Rsub *
        T.conjOperator (Jadj.comp (Q.comp J)) =
      scalar • T.conjOperator (Jadj.comp (Q.comp J)) := by
  have hleft : (J.comp Jadj).comp Q = Q :=
    isometricCompression_left_support_of_right_support J Jadj Q hJadj_eq hQ hright
  have hcompressed :
      (Jadj.comp (Q.comp J)) * Rsub * (Jadj.comp (Q.comp J)) =
        scalar • (Jadj.comp (Q.comp J)) :=
    isometricCompression_scalar_of_intertwining J Jadj Q R Rsub scalar hleft hscalar
      hintertwines
  exact unitaryTransport_conj_scalar_compression T
    (Jadj.comp (Q.comp J)) Rsub scalar hcompressed
end QEC.Bounds.BPTCommutingProjectorModel

-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_of_active_isometric_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:57:25.13834+00:00
-- url     : https://prove2.me/submissions/e7c0e7db-5cec-4419-857b-93d6e1fcfbdf

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Factorization
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ActiveProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isometricCompression_left_support_of_right_support
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_of_isometric_compression_commuting


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
    (hJadj : Jadj.comp J = (1 : Semantics.Operator H))
    (hJadj_eq : LinearMap.adjoint J = Jadj)
    (hQ : Q.IsSymmetricProjection)
    (hright : Q.comp (J.comp Jadj) = Q) :
    (Jadj.comp (Q.comp J)).IsSymmetricProjection := by
  have hleft := isometricCompression_left_support_of_right_support
    J Jadj Q hJadj_eq hQ hright
  apply isSymmetricProjection_of_isometric_compression_commuting J Jadj Q hJadj hJadj_eq hQ
  exact hright.trans hleft.symm
end QEC.Bounds.BPTCommutingProjectorModel

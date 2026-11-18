-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_lift_of_norm_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-18T04:23:46.492245+00:00
-- url     : https://prove2.me/submissions/6505fc4a-f2f3-439f-a8ce-07f018987128

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_comp_self_of_norm_map
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_isometric_lift


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
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (hnorm : ∀ x, ‖J x‖ = ‖x‖)
    (P : Semantics.Operator H) (hP : P.IsSymmetricProjection) :
    (J.comp (P.comp (LinearMap.adjoint J))).IsSymmetricProjection :=
  isSymmetricProjection_isometric_lift J (adjoint_comp_self_of_norm_map J hnorm) P hP
end QEC.Bounds.BPTCommutingProjectorModel

-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.tmul_left_eq_of_tmul_right_eq_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:04:18.175359+00:00
-- url     : https://prove2.me/submissions/78835c26-5c4b-48c2-9d08-51f92262eb4a

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_LeftPhysical
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ProjectionBlock

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
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    {left left' : H} (right : K) (hright : right ≠ 0)
    (h : left ⊗ₜ[Complex] right = left' ⊗ₜ[Complex] right) : left = left' := by
  have happly := congrArg (LinearMap.adjoint (overlapRightEmbedding H K right)) h
  rw [adjoint_overlapRightEmbedding_apply_tmul,
    adjoint_overlapRightEmbedding_apply_tmul] at happly
  have hinner : inner Complex right right ≠ 0 := inner_self_ne_zero.mpr hright
  calc
    left = (inner Complex right right)⁻¹ • ((inner Complex right right) • left) := by
      rw [smul_smul, inv_mul_cancel₀ hinner, one_smul]
    _ = (inner Complex right right)⁻¹ • ((inner Complex right right) • left') :=
      congrArg ((inner Complex right right)⁻¹ • ·) happly
    _ = left' := by rw [smul_smul, inv_mul_cancel₀ hinner, one_smul]
end QEC.Bounds.BPTCommutingProjectorModel

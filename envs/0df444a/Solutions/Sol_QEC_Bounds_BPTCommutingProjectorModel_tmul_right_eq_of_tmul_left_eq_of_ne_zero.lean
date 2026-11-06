-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.tmul_right_eq_of_tmul_left_eq_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:34:25.429279+00:00
-- url     : https://prove2.me/submissions/78f996bb-9ff0-43d4-a263-6daa56fcad38

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
    (left : H) (hleft : left ≠ 0) {right right' : K}
    (h : left ⊗ₜ[Complex] right = left ⊗ₜ[Complex] right') : right = right' := by
  have happly := congrArg (LinearMap.adjoint (overlapLeftEmbedding H K left)) h
  rw [adjoint_overlapLeftEmbedding_apply_tmul,
    adjoint_overlapLeftEmbedding_apply_tmul] at happly
  have hinner : inner Complex left left ≠ 0 := inner_self_ne_zero.mpr hleft
  calc
    right = (inner Complex left left)⁻¹ • ((inner Complex left left) • right) := by
      rw [smul_smul, inv_mul_cancel₀ hinner, one_smul]
    _ = (inner Complex left left)⁻¹ • ((inner Complex left left) • right') :=
      congrArg ((inner Complex left left)⁻¹ • ·) happly
    _ = right' := by rw [smul_smul, inv_mul_cancel₀ hinner, one_smul]
end QEC.Bounds.BPTCommutingProjectorModel

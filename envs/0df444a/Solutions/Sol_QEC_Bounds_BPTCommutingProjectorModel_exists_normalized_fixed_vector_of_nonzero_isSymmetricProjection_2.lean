-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.exists_normalized_fixed_vector_of_nonzero_isSymmetricProjection
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-06T00:09:10.520825+00:00
-- url     : https://prove2.me/submissions/4793ff0c-81bf-4515-9ab1-ffb2e8fb4f67

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Tensor
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualProjection
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
    {D : Type u} [NormedAddCommGroup D] [InnerProductSpace Complex D]
    [Semantics.FiniteQuantumSystem D]
    (P : Semantics.Operator D) (hP : P.IsSymmetricProjection) (hP0 : P ≠ 0) :
    ∃ eta : D, ‖eta‖ = 1 ∧ P eta = eta := by
  obtain ⟨x, hx⟩ : ∃ x, P x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hP0 (LinearMap.ext hcon)
  have hidem : ∀ v, P (P v) = P v := fun v => by
    have := hP.isIdempotentElem.eq
    exact congrArg (fun T : Semantics.Operator D => T v) this
  refine ⟨((‖P x‖ : Complex)⁻¹) • P x, norm_smul_inv_norm hx, ?_⟩
  rw [map_smul, hidem]

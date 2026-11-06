-- Prove2me | solution 1 for QEC.Semantics.JumpProtected.mul_of_commute_projector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:10:49.843386+00:00
-- url     : https://prove2.me/submissions/c0e51a9a-0677-4298-9da7-e4e5ae52aadb

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Theorems.Thm_QEC_Semantics_JumpProtected_jump_mul_observable_projector


set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped ComplexOrder
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
attribute [local instance] QEC.Semantics.clbtFiniteQuantumSystemComplete
namespace QEC.Semantics
namespace JumpProtected
theorem _root_.solution [Fintype ι]
    {J : ι → Operator H} {O₁ O₂ P : Operator H}
    (h₁ : JumpProtected J O₁ P) (h₂ : JumpProtected J O₂ P)
    (h₂P : Commute O₂ P) :
    JumpProtected J (O₁ * O₂) P := by
  intro a
  rw [show (J a * (O₁ * O₂) - O₁ * O₂ * J a) * P =
      J a * O₁ * O₂ * P - O₁ * O₂ * J a * P by noncomm_ring]
  have h₁a := h₁.jump_mul_observable_projector a
  have h₂a := h₂.jump_mul_observable_projector a
  calc
    J a * O₁ * O₂ * P - O₁ * O₂ * J a * P =
        J a * O₁ * (O₂ * P) - O₁ * O₂ * J a * P := by noncomm_ring
    _ = J a * O₁ * (P * O₂) - O₁ * O₂ * J a * P := by rw [h₂P.eq]
    _ = J a * O₁ * P * O₂ - O₁ * O₂ * J a * P := by noncomm_ring
    _ = O₁ * J a * P * O₂ - O₁ * O₂ * J a * P := by rw [h₁a]
    _ = O₁ * J a * (P * O₂) - O₁ * O₂ * J a * P := by noncomm_ring
    _ = O₁ * J a * (O₂ * P) - O₁ * O₂ * J a * P := by rw [h₂P.eq]
    _ = O₁ * J a * O₂ * P - O₁ * O₂ * J a * P := by noncomm_ring
    _ = O₁ * (J a * O₂ * P) - O₁ * O₂ * J a * P := by noncomm_ring
    _ = O₁ * (O₂ * J a * P) - O₁ * O₂ * J a * P := by rw [h₂a]
    _ = 0 := by noncomm_ring
end JumpProtected
end QEC.Semantics

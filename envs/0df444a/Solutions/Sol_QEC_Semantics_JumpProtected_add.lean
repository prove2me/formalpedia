-- Prove2me | solution 1 for QEC.Semantics.JumpProtected.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:10:07.333983+00:00
-- url     : https://prove2.me/submissions/0eb11ef2-8646-4dbb-8d54-91263725754d

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay

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
    (h₁ : JumpProtected J O₁ P) (h₂ : JumpProtected J O₂ P) :
    JumpProtected J (O₁ + O₂) P := by
  intro a
  rw [show (J a * (O₁ + O₂) - (O₁ + O₂) * J a) * P =
      (J a * O₁ - O₁ * J a) * P +
        (J a * O₂ - O₂ * J a) * P by noncomm_ring,
    h₁ a, h₂ a, add_zero]
end JumpProtected
end QEC.Semantics

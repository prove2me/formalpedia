-- Prove2me | solution 1 for QEC.Semantics.JumpProtected.jump_mul_observable_projector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:24:48.223469+00:00
-- url     : https://prove2.me/submissions/5ccf14d0-43e9-47e4-98c0-b4ba17ac0915

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator

set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
namespace QEC.Semantics
namespace JumpProtected
theorem _root_.solution [Fintype ι]
    {J : ι → Operator H} {O P : Operator H} (h : JumpProtected J O P) (a : ι) :
    J a * O * P = O * J a * P := by
  have ha := h a
  rw [sub_mul] at ha
  exact sub_eq_zero.mp ha
end JumpProtected
end QEC.Semantics

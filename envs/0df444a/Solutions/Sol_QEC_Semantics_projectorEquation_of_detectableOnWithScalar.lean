-- Prove2me | solution 1 for QEC.Semantics.projectorEquation_of_detectableOnWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:43:53.126374+00:00
-- url     : https://prove2.me/submissions/c71feda2-46c5-46a2-bcb2-b7b65607d6ba

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_adjoint_eq_self
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_idempotent
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_mem_carrier
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
noncomputable section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution
    {C : QuantumCode H} {E : Operator H} {c : Complex}
    (h : DetectableOnWithScalar C E c) :
    (C.projector.comp E).comp C.projector = c • C.projector := by
  ext v
  apply ext_inner_left Complex
  intro w
  have hinnerP :
      inner Complex (C.projector w) (C.projector v) =
        inner Complex w (C.projector v) := by
    have hAdj :=
      LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector w (C.projector v)
    have hIdemV : C.projector (C.projector v) = C.projector v := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun A : Operator H => A v) C.projector_idempotent
    simpa [C.projector_adjoint_eq_self, hIdemV] using hAdj.symm
  calc
    inner Complex w (((C.projector.comp E).comp C.projector) v) =
        inner Complex (C.projector w) (E (C.projector v)) := by
          have hAdj :=
            LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector w
              (E (C.projector v))
          simpa [LinearMap.comp_apply, C.projector_adjoint_eq_self] using hAdj
    _ = c * inner Complex (C.projector w) (C.projector v) :=
      h (C.projector w) (C.projector_mem_carrier w)
        (C.projector v) (C.projector_mem_carrier v)
    _ = c * inner Complex w (C.projector v) := by rw [hinnerP]
    _ = inner Complex w ((c • C.projector) v) := by simp
end QEC.Semantics

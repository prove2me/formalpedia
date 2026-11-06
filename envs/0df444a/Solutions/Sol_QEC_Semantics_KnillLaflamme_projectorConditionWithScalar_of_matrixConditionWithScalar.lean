-- Prove2me | solution 1 for QEC.Semantics.KnillLaflamme.projectorConditionWithScalar_of_matrixConditionWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:45:50.964381+00:00
-- url     : https://prove2.me/submissions/823dc777-d662-4f0d-a2d8-7b719aa6e3bb

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
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
open QEC.Semantics.KnillLaflamme
namespace QEC.Semantics.KnillLaflamme
theorem _root_.solution
    {C : QuantumCode H} {errors : Set (Operator H)}
    {scalar : Operator H → Operator H → Complex}
    (h : KnillLaflammeMatrixConditionWithScalar C errors scalar) :
    KnillLaflammeProjectorConditionWithScalar C errors scalar := by
  intro E hE F hF
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
    inner Complex w
        (((C.projector.comp ((LinearMap.adjoint E).comp F)).comp C.projector) v)
        = inner Complex (C.projector w)
            (((LinearMap.adjoint E).comp F) (C.projector v)) := by
          have hAdj :=
            LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector w
              (((LinearMap.adjoint E).comp F) (C.projector v))
          simpa [LinearMap.comp_apply, C.projector_adjoint_eq_self] using hAdj
    _ = inner Complex (E (C.projector w)) (F (C.projector v)) := by
          simpa [LinearMap.comp_apply] using
            (LinearMap.adjoint_inner_right (𝕜 := Complex) E (C.projector w)
              (F (C.projector v)))
    _ = scalar E F * inner Complex (C.projector w) (C.projector v) :=
          h hE hF (C.projector w) (C.projector_mem_carrier w)
            (C.projector v) (C.projector_mem_carrier v)
    _ = scalar E F * inner Complex w (C.projector v) := by
          rw [hinnerP]
    _ = inner Complex w ((scalar E F • C.projector) v) := by
          simp
end QEC.Semantics.KnillLaflamme

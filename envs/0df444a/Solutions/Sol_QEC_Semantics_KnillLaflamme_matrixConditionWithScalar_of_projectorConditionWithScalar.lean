-- Prove2me | solution 1 for QEC.Semantics.KnillLaflamme.matrixConditionWithScalar_of_projectorConditionWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:46:04.612962+00:00
-- url     : https://prove2.me/submissions/cb0a1c68-0437-4831-b361-1fd8403ba3fd

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_adjoint_eq_self
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_eq_self_of_mem
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
    (h : KnillLaflammeProjectorConditionWithScalar C errors scalar) :
    KnillLaflammeMatrixConditionWithScalar C errors scalar := by
  intro E hE F hF x hx y hy
  have hxP : C.projector x = x := C.projector_eq_self_of_mem hx
  have hyP : C.projector y = y := C.projector_eq_self_of_mem hy
  have hInsert :
      inner Complex x ((LinearMap.adjoint E) (F y)) =
        inner Complex x
          (C.projector (((LinearMap.adjoint E).comp F) (C.projector y))) := by
    have hAdj :=
      LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector x
        (((LinearMap.adjoint E).comp F) (C.projector y))
    simpa [LinearMap.comp_apply, C.projector_adjoint_eq_self, hxP, hyP] using
      hAdj.symm
  calc
    inner Complex (E x) (F y)
        = inner Complex x ((LinearMap.adjoint E) (F y)) := by
          simpa using
            (LinearMap.adjoint_inner_right (𝕜 := Complex) E x (F y)).symm
    _ = inner Complex x
          (C.projector (((LinearMap.adjoint E).comp F) (C.projector y))) :=
          hInsert
    _ = inner Complex x ((scalar E F • C.projector) y) := by
          simpa [LinearMap.comp_apply, hyP] using
            congrArg (fun z : H => inner Complex x z)
              (congrArg (fun A : Operator H => A y) (h hE hF))
    _ = scalar E F * inner Complex x y := by
          simp [hyP]
end QEC.Semantics.KnillLaflamme

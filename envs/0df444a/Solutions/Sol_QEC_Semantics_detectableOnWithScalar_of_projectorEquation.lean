-- Prove2me | solution 1 for QEC.Semantics.detectableOnWithScalar_of_projectorEquation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:44:53.108785+00:00
-- url     : https://prove2.me/submissions/eee04d5a-58b7-4e05-83df-98a741c1aade

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
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
namespace QEC.Semantics
theorem _root_.solution
    {C : QuantumCode H} {E : Operator H} {c : Complex}
    (h : (C.projector.comp E).comp C.projector = c • C.projector) :
    DetectableOnWithScalar C E c := by
  intro x hx y hy
  have hxP : C.projector x = x := C.projector_eq_self_of_mem hx
  have hyP : C.projector y = y := C.projector_eq_self_of_mem hy
  have hInsert :
      inner Complex x (E y) =
        inner Complex x (C.projector (E (C.projector y))) := by
    have hAdj :=
      LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector x
        (E (C.projector y))
    simpa [C.projector_adjoint_eq_self, hxP, hyP] using hAdj.symm
  calc
    inner Complex x (E y) =
        inner Complex x (C.projector (E (C.projector y))) := hInsert
    _ = inner Complex x ((c • C.projector) y) := by
      simpa [LinearMap.comp_apply, hyP] using
        congrArg (fun z : H => inner Complex x z)
          (congrArg (fun A : Operator H => A y) h)
    _ = c * inner Complex x y := by simp [hyP]
end QEC.Semantics

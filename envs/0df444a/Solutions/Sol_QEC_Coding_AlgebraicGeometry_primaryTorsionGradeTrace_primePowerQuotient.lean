-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionGradeTrace_primePowerQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:15:46.935398+00:00
-- url     : https://prove2.me/submissions/9bcf32c7-d344-4a50-a8d1-92f0958932b2

import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PrimePowerTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeEndomorphism_mk

section
namespace QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R]
private theorem primaryTorsionGradeEndomorphism_primePowerQuotientMul
    (q : R) (e i : ℕ) (r : R)
    (z : primaryTorsionGrade (Ideal.span {q})
      (R ⧸ Ideal.span {q ^ e}) i) :
    letI := primaryTorsionGradeModule
      (M := R ⧸ Ideal.span {q ^ e}) (Ideal.span {q}) i
    primaryTorsionGradeEndomorphism (Ideal.span {q})
        (primePowerQuotientMul q e r) i z =
      Ideal.Quotient.mk (Ideal.span {q}) r • z := by
  let h := primaryTorsionGrade_annihilated
    (R := R) (M := R ⧸ Ideal.span {q ^ e}) (Ideal.span {q}) i
  letI : Module (R ⧸ Ideal.span {q})
      (primaryTorsionGrade (Ideal.span {q})
        (R ⧸ Ideal.span {q ^ e}) i) := h.module
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
      rw [primaryTorsionGradeEndomorphism_mk,
        Module.IsTorsionBySet.mk_smul h]
      rfl
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsNoetherianRing R] (q : R) (hq : q ≠ 0)
    [hmax : (Ideal.span {q}).IsMaximal]
    (e i : ℕ) (hi : i < e) (r : R) :
    primaryTorsionGradeTrace (Ideal.span {q})
        (primePowerQuotientMul q e r) i =
      Ideal.Quotient.mk (Ideal.span {q}) r := by
  let p := Ideal.span {q}
  let M := R ⧸ Ideal.span {q ^ e}
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI := primaryTorsionGradeModule (M := M) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) :=
    primaryTorsionGradeFinite (M := M) p i
  let E := primaryTorsionGradeEquivPrimePowerQuotient q hq e i hi
  let source : (R ⧸ p) →ₗ[R ⧸ p] (R ⧸ p) :=
    Algebra.lmul (R ⧸ p) (R ⧸ p) (Ideal.Quotient.mk p r)
  let target : primaryTorsionGrade p M i →ₗ[R ⧸ p]
      primaryTorsionGrade p M i :=
    primaryTorsionGradeEndomorphism p (primePowerQuotientMul q e r) i
  have hconj : E.conj source = target := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := E.surjective z
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [primaryTorsionGradeEndomorphism_primePowerQuotientMul]
    exact E.map_smul (Ideal.Quotient.mk p r) x
  change LinearMap.trace (R ⧸ p) (primaryTorsionGrade p M i) target =
    Ideal.Quotient.mk p r
  calc
    _ = LinearMap.trace (R ⧸ p) (primaryTorsionGrade p M i)
        (E.conj source) := congrArg (LinearMap.trace (R ⧸ p) _) hconj.symm
    _ = LinearMap.trace (R ⧸ p) (R ⧸ p) source :=
      LinearMap.trace_conj' source E
    _ = Algebra.trace (R ⧸ p) (R ⧸ p) (Ideal.Quotient.mk p r) :=
      (Algebra.trace_apply (R ⧸ p) (Ideal.Quotient.mk p r)).symm
    _ = Ideal.Quotient.mk p r := Algebra.trace_self_apply _
end QEC.Coding.AlgebraicGeometry

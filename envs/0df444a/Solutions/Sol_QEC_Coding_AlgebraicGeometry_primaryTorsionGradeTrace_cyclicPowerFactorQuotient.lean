-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionGradeTrace_cyclicPowerFactorQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:15:49.598755+00:00
-- url     : https://prove2.me/submissions/310f42c2-839d-4567-aee9-0288ceb93b42

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PrimePowerTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicFactorTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeEndomorphism_mk

section
namespace QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R]
private theorem primaryTorsionGradeEndomorphism_cyclicPowerFactorQuotientMul
    (q : R) (e : ℕ) (b : R) (i : ℕ) (r : R)
    (z : primaryTorsionGrade (Ideal.span {q})
      (R ⧸ Ideal.span {q ^ e * b}) i) :
    letI := primaryTorsionGradeModule
      (M := R ⧸ Ideal.span {q ^ e * b}) (Ideal.span {q}) i
    primaryTorsionGradeEndomorphism (Ideal.span {q})
        (cyclicPowerFactorQuotientMul q e b r) i z =
      Ideal.Quotient.mk (Ideal.span {q}) r • z := by
  let h := primaryTorsionGrade_annihilated
    (R := R) (M := R ⧸ Ideal.span {q ^ e * b})
      (Ideal.span {q}) i
  letI : Module (R ⧸ Ideal.span {q})
      (primaryTorsionGrade (Ideal.span {q})
        (R ⧸ Ideal.span {q ^ e * b}) i) := h.module
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
    (e : ℕ) (b : R) (hb : b ≠ 0) (i : ℕ) (hi : i < e) (r : R) :
    primaryTorsionGradeTrace (Ideal.span {q})
        (cyclicPowerFactorQuotientMul q e b r) i =
      Ideal.Quotient.mk (Ideal.span {q}) r := by
  let p := Ideal.span {q}
  let M := R ⧸ Ideal.span {q ^ e * b}
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI := primaryTorsionGradeModule (M := M) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) :=
    primaryTorsionGradeFinite (M := M) p i
  let E := primaryTorsionGradeEquivCyclicPowerFactorQuotient
    q hq e b hb i hi
  let source : (R ⧸ p) →ₗ[R ⧸ p] (R ⧸ p) :=
    Algebra.lmul (R ⧸ p) (R ⧸ p) (Ideal.Quotient.mk p r)
  let target : primaryTorsionGrade p M i →ₗ[R ⧸ p]
      primaryTorsionGrade p M i :=
    primaryTorsionGradeEndomorphism p
      (cyclicPowerFactorQuotientMul q e b r) i
  have hconj : E.conj source = target := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := E.surjective z
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [primaryTorsionGradeEndomorphism_cyclicPowerFactorQuotientMul]
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

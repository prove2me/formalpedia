-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_primePowerQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:28:52.479657+00:00
-- url     : https://prove2.me/submissions/3ea5f1d7-51ba-463d-a1ea-8f118ca570f8

import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PrimePowerTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeTrace_primePowerQuotient

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsNoetherianRing R] (q : R) (hq : q ≠ 0)
    [hmax : (Ideal.span {q}).IsMaximal]
    (e : ℕ) (r : R) :
    primaryTorsionTrace (Ideal.span {q})
        (primePowerQuotientMul q e r) e =
      (e : R ⧸ Ideal.span {q}) *
        Ideal.Quotient.mk (Ideal.span {q}) r := by
  rw [primaryTorsionTrace]
  calc
    (∑ i ∈ Finset.range e,
        primaryTorsionGradeTrace (Ideal.span {q})
          (primePowerQuotientMul q e r) i) =
        ∑ _i ∈ Finset.range e,
          Ideal.Quotient.mk (Ideal.span {q}) r := by
      apply Finset.sum_congr rfl
      intro i hi
      exact primaryTorsionGradeTrace_primePowerQuotient q hq e i
        (Finset.mem_range.mp hi) r
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
end QEC.Coding.AlgebraicGeometry

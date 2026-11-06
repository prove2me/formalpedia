-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_cyclicPowerFactorQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:16:42.538206+00:00
-- url     : https://prove2.me/submissions/400e74e8-6e09-46a5-981e-25549257edc0

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PrimePowerTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicFactorTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionGradeTrace_cyclicPowerFactorQuotient

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsNoetherianRing R] (q : R) (hq : q ≠ 0)
    [hmax : (Ideal.span {q}).IsMaximal]
    (e : ℕ) (b : R) (hb : b ≠ 0) (r : R) :
    primaryTorsionTrace (Ideal.span {q})
        (cyclicPowerFactorQuotientMul q e b r) e =
      (e : R ⧸ Ideal.span {q}) *
        Ideal.Quotient.mk (Ideal.span {q}) r := by
  rw [primaryTorsionTrace]
  calc
    (∑ i ∈ Finset.range e,
        primaryTorsionGradeTrace (Ideal.span {q})
          (cyclicPowerFactorQuotientMul q e b r) i) =
        ∑ _i ∈ Finset.range e,
          Ideal.Quotient.mk (Ideal.span {q}) r := by
      apply Finset.sum_congr rfl
      intro i hi
      exact primaryTorsionGradeTrace_cyclicPowerFactorQuotient
        q hq e b hb i (Finset.mem_range.mp hi) r
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
end QEC.Coding.AlgebraicGeometry

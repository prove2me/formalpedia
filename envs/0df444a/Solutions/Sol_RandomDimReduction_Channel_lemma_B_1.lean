-- Prove2me | solution 1 for RandomDimReduction.Channel.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T03:25:54.889284+00:00
-- url     : https://prove2.me/submissions/4e320e3b-49c7-4eed-9072-11a4a9797137

import Definitions.Def_RandomDimReduction_Channel_Tensor

set_option autoImplicit false

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal
namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma B.1, p.22: D and E are independent rectangular operators. -/
theorem lemma_B_1 {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (X : Op (a × b)) (D E : Matrix c b ℂ) :
    WildeQIT.partialTraceRight
      (Matrix.kronecker (1 : Op a) D * X * Matrix.kronecker (1 : Op a) Eᴴ) =
    WildeQIT.partialTraceRight (Matrix.kronecker (1 : Op a) (Eᴴ * D) * X) := by
  ext i j
  simp only [WildeQIT.partialTraceRight, Matrix.of_apply, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x1 _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

end RandomDimReduction.Channel


open RandomDimReduction.Channel in
theorem solution {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (X : Op (a × b)) (D E : Matrix c b ℂ) :
    WildeQIT.partialTraceRight
      (Matrix.kronecker (1 : Op a) D * X * Matrix.kronecker (1 : Op a) Eᴴ) =
    WildeQIT.partialTraceRight (Matrix.kronecker (1 : Op a) (Eᴴ * D) * X) :=
  RandomDimReduction.Channel.lemma_B_1 X D E

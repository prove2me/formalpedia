-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P11.partialTrace_rightMultiply
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:45:42.808847+00:00
-- url     : https://prove2.me/submissions/d8734099-c879-4340-84e9-ba6665f6d620

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P11

noncomputable section

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Advance50.P11 in
theorem solution {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix A A ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    traceRight (rho * Matrix.kronecker sigma (1 : Matrix B B ℂ)) =
      traceRight rho * sigma := by
  ext j k
  simp only [traceRight, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Finset.sum_eq_single h]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply, hb]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

end

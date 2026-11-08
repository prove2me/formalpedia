-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P08.bell_transpose_identity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:05:22.810854+00:00
-- url     : https://prove2.me/submissions/adfd6894-a618-4476-8dc7-77aa6f97e6a5

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P08

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Extend50.P08 in
theorem solution (d : ℕ) (hd : 2 ≤ d) (X : Matrix (Fin d) (Fin d) ℂ) :
    QAlgorithms.act (Matrix.kronecker (1 : Matrix (Fin d) (Fin d) ℂ) X) (unnormalizedBell d) =
      QAlgorithms.act (Matrix.kronecker Xᵀ (1 : Matrix (Fin d) (Fin d) ℂ)) (unnormalizedBell d) := by
  unfold QAlgorithms.act unnormalizedBell
  congr 1
  funext p
  obtain ⟨i, j⟩ := p
  simp [Matrix.mulVec, dotProduct, Matrix.kronecker_apply, Matrix.one_apply,
    Fintype.sum_prod_type, ite_mul, mul_ite]

end

-- Prove2me | solution 1 for WeilConjectures.exists_snf_of_range_toLin_poly_matrix
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:44:50.890619+00:00
-- url     : https://prove2.me/submissions/090e33f6-6632-4272-a0c6-7a288fc936f0

import Mathlib

/-!
A48 RANGE-SNF-APPLY: direct Mathlib `Submodule.smithNormalForm` on
`LinearMap.range (toLin' M)` with `Pi.basisFun`. Free/PID discharged by
`Polynomial.instEuclideanDomain` + `Module.Free.function` (0-child).
-/

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∀ M : Matrix ι ι (Polynomial K),
      ∃ (n : ℕ),
        Nonempty
          (Module.Basis.SmithNormalForm
            (LinearMap.range (Matrix.toLin' M)) ι n) := by
  intro M
  let b := Pi.basisFun (Polynomial K) ι
  let snf := (LinearMap.range (Matrix.toLin' M)).smithNormalForm b
  exact ⟨snf.1, ⟨snf.2⟩⟩

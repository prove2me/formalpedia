-- Prove2me | solution 1 for centered_sampling_coefficient_variance_bound
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T21:08:13.474235+00:00
-- url     : https://prove2.me/submissions/e651fde5-9956-4bf7-86dd-a72045f9e8a6

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_centered_sampling_coefficient_second_moment
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

/-- `centered_sampling_coefficient_variance_bound`.

**Variance bound** `σ² ≤ ‖B‖_F²/p` for the scalar centered sampling coefficient.
From the exact second-moment identity `E[Coeff²] = ((1-p)/p)‖B‖_F²` and `1-p ≤ 1`
(for `p ∈ (0,1]`), together with `‖B‖_F² ≥ 0`, we get
`E[Coeff²] = ((1-p)/p)‖B‖_F² ≤ (1/p)‖B‖_F² = ‖B‖_F²/p`. This is the `σ²` quantity
fed into the q-moment Bernstein estimate. -/
theorem solution {n₁ n₂ : ℕ} (p : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    bernoulliExpectation p
      (fun Omega => (matrixEntrySum (centeredSamplingFluctuation Omega p B)) ^ 2) ≤
      frobeniusNormSq B / p := by
  classical
  rw [centered_sampling_coefficient_second_moment p (ne_of_gt hp0) B]
  have hfro : 0 ≤ frobeniusNormSq B := by
    unfold frobeniusNormSq
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    positivity
  -- ((1-p)/p)·F ≤ F/p  ⟺  (1-p)·F ≤ F  (multiply by p>0), and (1-p)F ≤ F since 0≤pF
  have hlhs : ((1 - p) / p) * frobeniusNormSq B = ((1 - p) * frobeniusNormSq B) / p := by
    rw [div_mul_eq_mul_div]
  rw [hlhs]
  gcongr
  nlinarith [hfro, hp0, hp1]

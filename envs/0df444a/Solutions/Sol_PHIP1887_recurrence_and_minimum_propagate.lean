-- Prove2me | solution 1 for PHIP1887.recurrence_and_minimum_propagate
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:47:13.124133+00:00
-- url     : https://prove2.me/submissions/bdb5fc91-668b-46ef-b062-bd94819478cb

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
import Theorems.Thm_PHIP1887_central_negative_step
open MeasureTheory Set
open PHIP1887

theorem solution
    (Q curvature : ℕ → ℝ → ℝ)
    (hrec : ∀ k x, 1 ≤ k → 0 < x →
      curvature k x = (k:ℝ)^2 * Q k x -
        2*(k:ℝ)*(2*(k:ℝ)+1)*Q (k+1) x)
    (hmin : ∀ k, 1 ≤ k → NegativeAt Q k →
      ∃ x, 0 < x ∧ Q k x < 0 ∧ 0 ≤ curvature k x) :
    ∀ k, 1 ≤ k → NegativeAt Q k → NegativeAt Q (k+1) := by
  intro k hk hneg
  obtain ⟨x, hx, hqx, hcx⟩ := hmin k hk hneg
  refine ⟨x, hx, ?_⟩
  have hkreal : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  exact central_negative_step (k:ℝ) (Q k x) (Q (k+1) x)
    (curvature k x) hkreal hqx hcx (hrec k x hk hx)

-- Prove2me | solution 1 for PDScenRed.Mean.pos_on_Z
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:15:37.943384+00:00
-- url     : https://prove2.me/submissions/b0bd4347-bc19-4866-aacc-cf264e0bb672

import Mathlib
import Definitions.Def_PDScenRed_Mean_Setting

set_option autoImplicit false
open scoped InnerProductSpace
open MeasureTheory PDScenRed.Mean

theorem solution {d r : ℕ} (P : Matrix (Fin r) (Fin d) ℝ) (qv : Fin r → ℝ)
    (zsel : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hsel : ∀ ξ, zsel ξ ∈ SmartPTO.Fisher.Wstar (polytope P qv) ξ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : 0 < ⟪zsel v, v⟫_ℝ) :
    ∀ z ∈ polytope P qv, ⟪zsel v, v⟫_ℝ ≤ ⟪z, v⟫_ℝ ∧ 0 < ⟪z, v⟫_ℝ := by
  intro z hz
  have h := (hsel v).2 z hz
  rw [real_inner_comm (zsel v) v, real_inner_comm z v] at h
  exact ⟨h, lt_of_lt_of_le hv h⟩

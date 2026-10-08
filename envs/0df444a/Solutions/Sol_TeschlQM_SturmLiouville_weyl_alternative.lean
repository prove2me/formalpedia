-- Prove2me | solution 1 for TeschlQM.SturmLiouville.weyl_alternative
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-04T20:10:24.834986+00:00
-- url     : https://prove2.me/submissions/1ef5f375-1be3-4080-b9d8-759300f72f58

import Theorems.Thm_TeschlQM_SturmLiouville_sqIntegrable_all_z
import Theorems.Thm_TeschlQM_SturmLiouville_limitCircle_of_sqIntegrable
import Theorems.Thm_TeschlQM_SturmLiouville_sqIntegrable_of_limitCircle

open TeschlQM.SturmLiouville

theorem solution (L : SLData) :
    (IsLimitCircleLeft L ↔
        ∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearLeft L u) ∧
      (IsLimitCircleLeft L →
        ∀ z : ℂ, ∀ u : ℝ → ℂ, IsSolution L z 0 u → IsSqIntegrableNearLeft L u) ∧
      (IsLimitCircleRight L ↔
        ∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearRight L u) ∧
      (IsLimitCircleRight L →
        ∀ z : ℂ, ∀ u : ℝ → ℂ, IsSolution L z 0 u → IsSqIntegrableNearRight L u) := by
  obtain ⟨P1, P2⟩ := sqIntegrable_all_z L
  obtain ⟨C1, C2⟩ := limitCircle_of_sqIntegrable L 0
  obtain ⟨S1, S2⟩ := sqIntegrable_of_limitCircle L
  refine ⟨⟨S1, fun h => C1 (by simpa using P1 h 0)⟩, fun h => P1 (S1 h),
    ⟨S2, fun h => C2 (by simpa using P2 h 0)⟩, fun h => P2 (S2 h)⟩

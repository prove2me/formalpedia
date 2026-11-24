-- Prove2me | solution 1 for ValiantBorder.exactLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:07:50.95639+00:00
-- url     : https://prove2.me/submissions/45298550-794f-4cc6-bb7b-c5f794c6a1fc

import Theorems.Thm_ValiantBorder_allFields
import Theorems.Thm_ValiantBorder_exactIsApprox

universe u

/-- Theorem 1.1 from Theorem 1.4 of Claude (Anthropic), *VP ≠ VNP over every field*. -/
theorem solution : Statement.MainTheorem.{u} := by
  obtain ⟨c, hc, bound⟩ := ValiantBorder.allFields.{u}.1
  refine ⟨c, hc, fun p => ?_⟩
  obtain ⟨m₀, threshold⟩ := bound p
  refine ⟨m₀, fun F _ _ m hm s => ?_⟩
  obtain ⟨hhc, hperm⟩ := threshold F m hm s
  exact ⟨fun h => hhc (ValiantBorder.exactIsApprox _ _ h),
    fun hp h => hperm hp (ValiantBorder.exactIsApprox _ _ h)⟩

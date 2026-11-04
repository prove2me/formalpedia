-- Prove2me | solution 1 for ThreeSum.PrimeDensity.mem_candidates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:53:57.342984+00:00
-- url     : https://prove2.me/submissions/334c5f87-e88d-4b6b-8ca1-2e3f6618dc4f

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Submission_ThreeSum_PrimeDensity

set_option autoImplicit false
open ThreeSum ThreeSum.PrimeDensity
open Real Filter Finset
open scoped Topology
noncomputable section
namespace ThreeSum.PrimeDensity
theorem _root_.solution {p y : ℕ} :
    p ∈ candidates y ↔ Nat.Prime p ∧ y < p ∧ p ≤ 4 * y := by
  unfold candidates
  rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp4, hp⟩, hn⟩
    refine ⟨hp, ?_, hp4⟩
    by_contra h
    exact hn ⟨by omega, hp⟩
  · rintro ⟨hp, hyp, hp4⟩
    exact ⟨⟨hp4, hp⟩, fun h => (not_le_of_gt hyp) h.1⟩
end ThreeSum.PrimeDensity

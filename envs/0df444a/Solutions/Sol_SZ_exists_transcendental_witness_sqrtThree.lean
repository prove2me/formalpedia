-- Prove2me | solution 1 for SZ.exists_transcendental_witness_sqrtThree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:40:14.992341+00:00
-- url     : https://prove2.me/submissions/43454792-9372-4f44-8909-5d6666764d44

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_exists_transcendental_mem_witnessSet

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution :
    ∃ ξ : ℝ, ξ ≠ 0 ∧ Transcendental ℚ ξ ∧
      ∀ n : ℕ, 1 ≤ n → Even ⌊ξ * Real.sqrt 3 ^ n⌋ := by
  obtain ⟨ξ, ⟨hpos, hfloor⟩, htr⟩ := exists_transcendental_mem_witnessSet
  exact ⟨ξ, ne_of_gt hpos, htr, hfloor⟩
end SZ

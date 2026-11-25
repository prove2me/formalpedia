-- Prove2me | solution 1 for SZ.exists_transcendental_mem_witnessSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:35:31.425819+00:00
-- url     : https://prove2.me/submissions/2bd6030b-3c02-4a42-bf3a-9b823a6431fa

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_not_countable_witnessSet

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution :
    ∃ ξ ∈ witnessSet, Transcendental ℚ ξ := by
  by_contra hcon
  push Not at hcon
  have hsub : witnessSet ⊆ {x : ℝ | IsAlgebraic ℚ x} := fun ξ hξ => not_not.mp (hcon ξ hξ)
  exact not_countable_witnessSet ((Algebraic.countable ℚ ℝ).mono hsub)
end SZ

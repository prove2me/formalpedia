-- Prove2me | solution 1 for SoficGroups.ThompsonFFiniteQuotient.conjugacy_relation_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/6f44e480-26cc-4f37-a41e-63bb5c6a4027

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonFFiniteQuotient_conjugateTerm_succ
import Theorems.Thm_SoficGroups_ThompsonFFiniteQuotient_conjugation_shift

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFFiniteQuotient
variable {G : Type*} [Group G]
namespace SoficGroups.ThompsonFFiniteQuotient
theorem _root_.solution (a b u : G) (n : ℕ)
    (h : u⁻¹ * conjugateTerm a b n * u =
      conjugateTerm a b (n + 1)) :
    (a⁻¹ * u * a)⁻¹ * conjugateTerm a b (n + 1) *
        (a⁻¹ * u * a) = conjugateTerm a b (n + 2) := by
  rw [conjugateTerm_succ a b n,
    conjugateTerm_succ a b (n + 1)]
  exact conjugation_shift a u
    (conjugateTerm a b n) (conjugateTerm a b (n + 1)) h
end SoficGroups.ThompsonFFiniteQuotient

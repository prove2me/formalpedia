-- Prove2me | solution 1 for SoficGroups.ThompsonFFiniteQuotient.conjugateTerm_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/ab09b541-3da4-4f1c-b458-ed34c43e023f

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFFiniteQuotient
variable {G : Type*} [Group G]
namespace SoficGroups.ThompsonFFiniteQuotient
theorem _root_.solution (a b : G) (n : ℕ) :
    conjugateTerm a b (n + 1) =
      a⁻¹ * conjugateTerm a b n * a := by
  simp only [conjugateTerm, pow_succ, mul_inv_rev]
  group
end SoficGroups.ThompsonFFiniteQuotient

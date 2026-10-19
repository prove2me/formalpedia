-- Prove2me | solution 1 for SoficGroups.ThompsonFFiniteQuotient.conjugacy_relation_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/c8f208d5-9a06-46bf-9ba2-16826c66d2f2

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonFFiniteQuotient_conjugacy_relation_step

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFFiniteQuotient
variable {G : Type*} [Group G]
namespace SoficGroups.ThompsonFFiniteQuotient
theorem _root_.solution (a b : G)
    (hfirst : b⁻¹ * conjugateTerm a b 1 * b =
      conjugateTerm a b 2)
    (hsecond : b⁻¹ * conjugateTerm a b 2 * b =
      conjugateTerm a b 3) (n : ℕ) :
    b⁻¹ * conjugateTerm a b (n + 1) * b =
      conjugateTerm a b (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => exact hfirst
  | one => exact hsecond
  | more n hprevious hcurrent =>
      simpa [Nat.add_assoc] using
        conjugacy_relation_step a b (n + 1)
          hfirst hprevious hcurrent
end SoficGroups.ThompsonFFiniteQuotient

-- Prove2me | solution 1 for SoficGroups.ThompsonFFiniteQuotient.conjugacy_relation_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/4fa2ef0e-5d24-4aca-bc4f-ccb1c9ff0ee4

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonFFiniteQuotient_conjugateTerm_succ
import Theorems.Thm_SoficGroups_ThompsonFFiniteQuotient_conjugacy_relation_shift

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFFiniteQuotient
variable {G : Type*} [Group G]
namespace SoficGroups.ThompsonFFiniteQuotient
theorem _root_.solution (a b : G) (n : ℕ)
    (hfirst : b⁻¹ * conjugateTerm a b 1 * b =
      conjugateTerm a b 2)
    (hprevious : b⁻¹ * conjugateTerm a b n * b =
      conjugateTerm a b (n + 1))
    (hcurrent : b⁻¹ * conjugateTerm a b (n + 1) * b =
      conjugateTerm a b (n + 2)) :
    b⁻¹ * conjugateTerm a b (n + 2) * b =
      conjugateTerm a b (n + 3) := by
  have hone : conjugateTerm a b 1 = a⁻¹ * b * a := by
    simp [conjugateTerm]
  have hshift :
      (conjugateTerm a b 1)⁻¹ *
          conjugateTerm a b (n + 1) *
          conjugateTerm a b 1 =
        conjugateTerm a b (n + 2) := by
    rw [hone]
    exact conjugacy_relation_shift a b b n hprevious
  have hdouble :
      (conjugateTerm a b 2)⁻¹ *
          conjugateTerm a b (n + 2) *
          conjugateTerm a b 2 =
        conjugateTerm a b (n + 3) := by
    rw [conjugateTerm_succ a b 1]
    exact conjugacy_relation_shift a b
      (conjugateTerm a b 1) (n + 1) hshift
  calc
    b⁻¹ * conjugateTerm a b (n + 2) * b =
        (b⁻¹ * conjugateTerm a b 1 * b)⁻¹ *
          (b⁻¹ * conjugateTerm a b (n + 1) * b) *
          (b⁻¹ * conjugateTerm a b 1 * b) := by
      rw [← hshift]
      group
    _ = (conjugateTerm a b 2)⁻¹ *
          conjugateTerm a b (n + 2) *
          conjugateTerm a b 2 := by
      rw [hfirst, hcurrent]
    _ = conjugateTerm a b (n + 3) := hdouble
end SoficGroups.ThompsonFFiniteQuotient

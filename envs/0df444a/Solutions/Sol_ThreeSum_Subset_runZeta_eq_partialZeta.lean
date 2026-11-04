-- Prove2me | solution 1 for ThreeSum.Subset.runZeta_eq_partialZeta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:53.082116+00:00
-- url     : https://prove2.me/submissions/29e78642-c67a-4c9b-9c87-b21ca3dae53d

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Aesop
import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_WeightedCache3SUM_Alias_790a7eeb73d26fe5

set_option autoImplicit false
open ThreeSum ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.Subset
theorem _root_.solution (coords : List α) (hn : coords.Nodup)
    (f : Finset α → ℤ) (u : Finset α) :
    runZeta coords f u = partialZeta coords.toFinset f u := by
  induction coords generalizing u with
  | nil => simp [runZeta, partialZeta]
  | cons a coords ih =>
      have hparts := List.nodup_cons.mp hn
      have hnot : a ∉ coords.toFinset := by simpa using hparts.1
      have heq : runZeta coords f = partialZeta coords.toFinset f := by
        funext v
        exact ih hparts.2 v
      simp only [runZeta, List.toFinset_cons, heq]
      exact (partialZeta_insert f u coords.toFinset a hnot).symm
end ThreeSum.Subset

-- Prove2me | solution 1 for ThreeSum.Subset.mobius_zeta_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:20.879759+00:00
-- url     : https://prove2.me/submissions/87a0978b-9d78-421e-8717-fc69a6d93ce7

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
import Theorems.Thm_ThreeSum_Subset_zeta_insert
import Theorems.Thm_ThreeSum_Subset_mobius_congr
import Theorems.Thm_ThreeSum_Subset_mobius_add
import Theorems.Thm_ThreeSum_Subset_mobius_insert

set_option autoImplicit false
open ThreeSum ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.Subset
theorem _root_.solution (f : Finset α → ℤ) (q : Finset α) :
    mobius (zeta f) q = f q := by
  induction q using Finset.induction_on generalizing f with
  | empty => simp [mobius, zeta]
  | @insert a q ha ih =>
      rw [mobius_insert (zeta f) ha]
      have hchange :
          mobius (fun s => zeta f (insert a s)) q =
          mobius (fun s => zeta f s + zeta (fun t => f (insert a t)) s) q := by
        apply mobius_congr
        intro s hs
        exact zeta_insert f (fun h => ha (hs h))
      rw [hchange, mobius_add, ih f, ih (fun s => f (insert a s))]
      ring
end ThreeSum.Subset

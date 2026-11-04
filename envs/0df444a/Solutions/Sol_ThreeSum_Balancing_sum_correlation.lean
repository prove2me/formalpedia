-- Prove2me | solution 1 for ThreeSum.Balancing.sum_correlation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:48.332584+00:00
-- url     : https://prove2.me/submissions/dea697f7-f43d-4f61-b98c-5c7123e0b704

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_Balancing

set_option autoImplicit false
open ThreeSum ThreeSum.Balancing
open Finset
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G]
namespace ThreeSum.Balancing
theorem _root_.solution (F H : G → ℕ) :
    (∑ d, correlation F H d) = (∑ k, F k) * (∑ k, H k) := by
  unfold correlation
  rw [sum_comm]
  simp only [← mul_sum]
  have hshift (k : G) : (∑ d, H (k - d)) = ∑ d, H d := by
    exact Equiv.sum_comp (Equiv.subLeft k) H
  simp_rw [hshift]
  exact (sum_mul ..).symm
end ThreeSum.Balancing

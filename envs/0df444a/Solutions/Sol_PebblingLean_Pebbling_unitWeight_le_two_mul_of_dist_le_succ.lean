-- Prove2me | solution 1 for PebblingLean.Pebbling.unitWeight_le_two_mul_of_dist_le_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:45.529894+00:00
-- url     : https://prove2.me/submissions/a37128a7-889e-497f-bdd9-7ab6f15a797d

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_PebblingLean_Weight

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution (dist : V → V → ℕ) {u v target : V}
    (h : dist u target ≤ dist v target + 1) :
    unitWeight dist target v ≤ 2 * unitWeight dist target u := by
  unfold unitWeight
  have hbase_one : (1 : ℚ) ≤ 2 := by norm_num
  have hpow : (2 : ℚ) ^ dist u target ≤ (2 : ℚ) ^ (dist v target + 1) := by
    exact pow_le_pow_right₀ hbase_one h
  rw [pow_succ] at hpow
  have hpu : 0 < (2 : ℚ) ^ dist u target := by positivity
  have hpv : 0 < (2 : ℚ) ^ dist v target := by positivity
  field_simp [hpu.ne', hpv.ne']
  linarith
end PebblingLean.Pebbling

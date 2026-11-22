-- Prove2me | solution 1 for PebblingLean.Pebbling.sum_moveDistribution_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:41.815546+00:00
-- url     : https://prove2.me/submissions/edcd727a-14f2-4f76-bb76-834fbb5e0b8e

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
public import Theorems.Thm_PebblingLean_Pebbling_weight_zero
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero


attribute [local simp] PebblingLean.Pebbling.weight_zero

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [Fintype V] [DecidableEq V] (D : Pebbling V)
    (w : V → ℚ) {u v : V} (huv : u ≠ v) (hD : 2 ≤ D u) :
    (∑ x, ((moveDistribution D u v x : ℕ) : ℚ) * w x)
      = (∑ x, (D x : ℚ) * w x) - 2 * w u + w v := by
  classical
  have hcast : ((D u - 2 : ℕ) : ℚ) = (D u : ℚ) - 2 := by
    simp_all
  have hpoint :
      ∀ x : V,
        ((moveDistribution D u v x : ℕ) : ℚ) * w x =
          (D x : ℚ) * w x +
            (if u = x then -2 * w u else if v = x then w v else 0) := by
    intro x
    by_cases hux : u = x
    · subst x
      simp [moveDistribution, hcast]
      ring
    · by_cases hvx : v = x
      · subst x
        have hvu : v ≠ u := fun h => hux h.symm
        simp [moveDistribution, hvu]
        simp [hux]
        ring_nf
      · have hxu : x ≠ u := fun h => hux h.symm
        have hxv : x ≠ v := fun h => hvx h.symm
        simp_all
  calc
    (∑ x, ((moveDistribution D u v x : ℕ) : ℚ) * w x)
        = ∑ x, ((D x : ℚ) * w x +
            (if u = x then -2 * w u else if v = x then w v else 0)) := by
          exact Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = (∑ x, (D x : ℚ) * w x) +
          (∑ x, (if u = x then -2 * w u else if v = x then w v else 0)) := by
          exact Finset.sum_add_distrib
    _ = (∑ x, (D x : ℚ) * w x) - 2 * w u + w v := by
          have hdelta :
              (∑ x : V, if u = x then -2 * w u else if v = x then w v else 0)
                = -2 * w u + w v := by
            calc
              (∑ x : V, if u = x then -2 * w u else if v = x then w v else 0)
                  = ∑ x : V, ((if u = x then -2 * w u else 0) +
                      (if v = x then w v else 0)) := by
                    apply Finset.sum_congr rfl
                    intro x _
                    by_cases hux : u = x
                    · have hvx_false : ¬ v = x := fun hvx => huv (hux.trans hvx.symm)
                      simp [hux, hvx_false]
                    · simp_all
              _ = (∑ x : V, if u = x then -2 * w u else 0) +
                    (∑ x : V, if v = x then w v else 0) := by
                    exact Finset.sum_add_distrib
              _ = -2 * w u + w v := by
                    simp_all
          rw [hdelta]
          ring_nf
end PebblingLean.Pebbling

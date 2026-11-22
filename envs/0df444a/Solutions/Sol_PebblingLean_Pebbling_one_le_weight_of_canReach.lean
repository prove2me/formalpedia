-- Prove2me | solution 1 for PebblingLean.Pebbling.one_le_weight_of_canReach
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:04:18.775988+00:00
-- url     : https://prove2.me/submissions/aee8859a-96d4-4dfd-80ba-ba14c52df3f8

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
public import Theorems.Thm_PebblingLean_Pebbling_weight_reaches_le_of_dist
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
theorem _root_.solution [Fintype V] [DecidableEq V] (G : Graph V)
    (dist : V → V → ℕ) {D : Pebbling V} {target : V}
    (hcan : CanReach G D target)
    (hdist_self : dist target target = 0)
    (hdist_edge : ∀ {u v : V}, G.Adj u v → dist u target ≤ dist v target + 1) :
    1 ≤ weight dist D target := by
  rcases hcan with ⟨E, hreach, htarget⟩
  have hmono := weight_reaches_le_of_dist (G := G) (dist := dist)
    (D := D) (E := E) (target := target) hreach hdist_edge
  have hterm : 1 ≤ (E target : ℚ) * unitWeight dist target target := by
    have htarget_rat : (1 : ℚ) ≤ (E target : ℚ) := by
      exact_mod_cast htarget
    simpa [unitWeight, hdist_self] using htarget_rat
  have hnonneg :
      ∀ x ∈ (Finset.univ : Finset V), 0 ≤ (E x : ℚ) * unitWeight dist target x := by
    intro x _
    have hpow_pos : 0 < (2 : ℚ) ^ dist x target := by positivity
    have hunit_nonneg : 0 ≤ unitWeight dist target x := by
      unfold unitWeight
      exact div_nonneg zero_le_one hpow_pos.le
    exact mul_nonneg (Nat.cast_nonneg _) hunit_nonneg
  have hEweight : 1 ≤ weight dist E target := by
    exact hterm.trans (Finset.single_le_sum hnonneg (Finset.mem_univ target))
  exact hEweight.trans hmono
end PebblingLean.Pebbling

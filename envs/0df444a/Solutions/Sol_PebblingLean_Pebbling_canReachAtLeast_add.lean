-- Prove2me | solution 1 for PebblingLean.Pebbling.canReachAtLeast_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:04:03.985406+00:00
-- url     : https://prove2.me/submissions/1bf2d616-97a5-4bd5-b6fd-b5ea7d7619b9

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_PebblingLean_Delivery
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_self
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_size_single
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_left
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_right
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_reaches_add_right
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero


attribute [local simp] PebblingLean.Graph.Walk.length_append
attribute [local simp] PebblingLean.Graph.Walk.length_reverse
attribute [local simp] PebblingLean.Pebbling.single_apply_self
attribute [local simp] PebblingLean.Pebbling.single_apply_ne
attribute [local simp] PebblingLean.Pebbling.size_single
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_left
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_right
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_ne

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] {G : Graph V} {D₁ D₂ : Pebbling V}
    {target : V} {T₁ T₂ : ℕ}
    (h₁ : CanReachAtLeast G D₁ target T₁)
    (h₂ : CanReachAtLeast G D₂ target T₂) :
    CanReachAtLeast G (D₁ + D₂) target (T₁ + T₂) := by
  rcases h₁ with ⟨E₁, hreach₁, htarget₁⟩
  rcases h₂ with ⟨E₂, hreach₂, htarget₂⟩
  have hfirst : Reaches G (D₁ + D₂) (E₁ + D₂) :=
    reaches_add_right hreach₁
  have hsecond₀ : Reaches G (D₂ + E₁) (E₂ + E₁) :=
    reaches_add_right hreach₂
  have hstart : D₂ + E₁ = E₁ + D₂ := by
    funext v
    exact Nat.add_comm (D₂ v) (E₁ v)
  have hfinish : E₂ + E₁ = E₁ + E₂ := by
    funext v
    exact Nat.add_comm (E₂ v) (E₁ v)
  have hsecond : Reaches G (E₁ + D₂) (E₁ + E₂) := by
    simpa [hstart, hfinish] using hsecond₀
  refine ⟨E₁ + E₂, Relation.ReflTransGen.trans hfirst hsecond, ?_⟩
  exact add_le_add htarget₁ htarget₂
end PebblingLean.Pebbling

-- Prove2me | solution 1 for PebblingLean.Pebbling.fibers_reaches_of_forall_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:57.483379+00:00
-- url     : https://prove2.me/submissions/2d40a8d6-275a-41e6-95a5-f9c2a4cb98e0

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Theorems.Thm_PebblingLean_Pebbling_fibersDistribution_apply
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_on
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_off
public import Theorems.Thm_PebblingLean_Pebbling_replaceFiber_reaches_left
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero


attribute [local simp] PebblingLean.Pebbling.fibersDistribution_apply
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_on
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_off

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.Pebbling
variable {V : Type u} {W : Type v}
namespace PebblingLean.Pebbling
theorem _root_.solution [Finite W] [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {F F' : W → Pebbling V}
    (hreach : ∀ z : W, Reaches G (F z) (F' z)) :
    Reaches (Graph.cartesianProduct G H) (fibersDistribution F) (fibersDistribution F') := by
  classical
  let := Fintype.ofFinite W
  have hstep :
      ∀ s : Finset W,
        Reaches (Graph.cartesianProduct G H)
          (fibersDistribution F)
          (fibersDistribution (updateFibers F F' s)) := by
    intro s
    refine Finset.induction_on s ?base ?insert
    · have hbase :
          fibersDistribution (updateFibers F F' ∅) = fibersDistribution F := by
        funext p
        cases p with
        | mk x z =>
          simp [fibersDistribution, updateFibers]
      rw [hbase]
      exact Relation.ReflTransGen.refl
    · intro z s hz_not_mem ih
      have hreplace :
          Reaches (Graph.cartesianProduct G H)
            (fibersDistribution (replaceFiber (updateFibers F F' s) z (F z)))
            (fibersDistribution (replaceFiber (updateFibers F F' s) z (F' z))) :=
        replaceFiber_reaches_left (G := G) (H := H)
          (Fs := updateFibers F F' s) (z := z) (hreach z)
      have hstart :
          fibersDistribution (replaceFiber (updateFibers F F' s) z (F z)) =
            fibersDistribution (updateFibers F F' s) := by
        funext p
        cases p with
        | mk x z' =>
          by_cases hz' : z' = z
          · subst z'
            simp [fibersDistribution, replaceFiber, updateFibers, hz_not_mem]
          · simp [fibersDistribution, replaceFiber, updateFibers, hz']
      have hfinish :
          fibersDistribution (replaceFiber (updateFibers F F' s) z (F' z)) =
            fibersDistribution (updateFibers F F' (insert z s)) := by
        funext p
        cases p with
        | mk x z' =>
          by_cases hz' : z' = z
          · subst z'
            simp [fibersDistribution, replaceFiber, updateFibers]
          · simp [fibersDistribution, replaceFiber, updateFibers, hz']
      have hreplace' :
          Reaches (Graph.cartesianProduct G H)
            (fibersDistribution (updateFibers F F' s))
            (fibersDistribution (updateFibers F F' (insert z s))) := by
        simpa [hstart, hfinish] using hreplace
      exact Relation.ReflTransGen.trans ih hreplace'
  have hfinal : fibersDistribution (updateFibers F F' Finset.univ) = fibersDistribution F' := by
    funext p
    cases p with
    | mk x z =>
      simp [fibersDistribution, updateFibers]
  simpa [hfinal] using hstep Finset.univ
end PebblingLean.Pebbling

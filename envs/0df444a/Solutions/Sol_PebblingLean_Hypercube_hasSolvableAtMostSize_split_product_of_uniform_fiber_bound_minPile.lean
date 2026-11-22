-- Prove2me | solution 1 for PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_uniform_fiber_bound_minPile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:28.302913+00:00
-- url     : https://prove2.me/submissions/8d174566-d36b-460f-9a9f-6111fd3517e7

module
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finite.Prod
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_split_product_of_uniform_fiber_bound
public import Theorems.Thm_PebblingLean_Pebbling_hasSolvableAtMostSize_mono_size
public import Theorems.Thm_PebblingLean_Pebbling_supportSize_mul_minPileCost_le_size_mul


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {a m Tbase Tfiber S K : ℕ} {E : Pebbling (HypercubeVertex m)}
    (hTbase : 1 ≤ Tbase)
    (hE : Pebbling.SolvableAtLeast (graph m) E Tbase)
    (hpile_le : ∀ z : HypercubeVertex m, E z ≤ Tfiber)
    (hmin : Pebbling.MinOccupiedPileSize E S)
    (hfiber : Pebbling.HasSolvableAtMostSize (graph a) Tfiber (S * K)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (Pebbling.size E * K) := by
  have hprod :=
    hasSolvableAtMostSize_split_product_of_uniform_fiber_bound
      (a := a) (m := m) (Tbase := Tbase) (Tfiber := Tfiber)
      (K := S * K) (E := E)
      hTbase hE hpile_le hfiber
  exact Pebbling.hasSolvableAtMostSize_mono_size
    (Pebbling.supportSize_mul_minPileCost_le_size_mul hmin) hprod
end PebblingLean.Hypercube

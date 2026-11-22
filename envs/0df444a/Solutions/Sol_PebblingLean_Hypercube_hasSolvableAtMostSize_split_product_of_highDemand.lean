-- Prove2me | solution 1 for PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_highDemand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:58.316567+00:00
-- url     : https://prove2.me/submissions/4ba0b415-589e-43c6-b419-20eb5c8aa51b

module
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finite.Prod
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_split_product_of_uniform_fiber_bound_minPile
public import Theorems.Thm_PebblingLean_Pebbling_hasSolvableAtMostSize_mono_size
public import Theorems.Thm_PebblingLean_Pebbling_le_size


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {a m Tbase costBound S K : ℕ}
    (hTbase : 1 ≤ Tbase)
    (hhigh : HasHighDemandDistribution m Tbase costBound S)
    (hfiber : Pebbling.HasSolvableAtMostSize (graph a) costBound (S * K)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1 (costBound * K) := by
  rcases hhigh with ⟨E, hsize, hE, hmin⟩
  have hpile_le : ∀ z : HypercubeVertex m, E z ≤ costBound := by
    intro z
    exact (Pebbling.le_size E z).trans hsize
  have hprod :=
    hasSolvableAtMostSize_split_product_of_uniform_fiber_bound_minPile
      (a := a) (m := m) (Tbase := Tbase) (Tfiber := costBound)
      (S := S) (K := K) (E := E)
      hTbase hE hpile_le hmin hfiber
  exact Pebbling.hasSolvableAtMostSize_mono_size
    (Nat.mul_le_mul_right K hsize) hprod
end PebblingLean.Hypercube

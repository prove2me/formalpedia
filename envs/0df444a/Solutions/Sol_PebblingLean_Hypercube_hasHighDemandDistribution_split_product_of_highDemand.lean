-- Prove2me | solution 1 for PebblingLean.Hypercube.hasHighDemandDistribution_split_product_of_highDemand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:05:02.519327+00:00
-- url     : https://prove2.me/submissions/0d0fe791-d6a1-4564-a551-a06cd2793283

module
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finite.Prod
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Theorems.Thm_PebblingLean_GraphIso_map_minOccupiedPileSize
public import Theorems.Thm_PebblingLean_GraphIso_map_solvableAtLeast
public import Theorems.Thm_PebblingLean_GraphIso_size_mapDistribution
public import Theorems.Thm_PebblingLean_Hypercube_mem_annulus
public import Theorems.Thm_PebblingLean_Pebbling_fibersDistribution_apply
public import Theorems.Thm_PebblingLean_Pebbling_le_size
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_fibersDistribution_le
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_off
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_on
public import Theorems.Thm_PebblingLean_Pebbling_solvableAtLeast_mono
public import Theorems.Thm_PebblingLean_Pebbling_solvableAtLeast_zero
public import Theorems.Thm_PebblingLean_Pebbling_solvable_of_solvableAtLeast
public import Theorems.Thm_PebblingLean_Pebbling_solvable_product_of_fiber_demands
public import Theorems.Thm_PebblingLean_Pebbling_sum_ite_nonzero_const
public import Theorems.Thm_PebblingLean_Pebbling_supportSize_mul_minPileCost_le_size_mul
attribute [local simp] PebblingLean.Hypercube.mem_annulus
attribute [local simp] PebblingLean.Pebbling.fibersDistribution_apply
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_off
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_on



set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {a m Tbase costBound S K Snew : ℕ}
    (hTbase : 1 ≤ Tbase)
    (hhigh : HasHighDemandDistribution m Tbase costBound S)
    (hfiber : HasHighDemandDistribution a costBound (S * K) Snew) :
    HasHighDemandDistribution (a + m) 1 (costBound * K) Snew := by
  classical
  rcases hhigh with ⟨E, hEsize, hEsolv, hEmin⟩
  rcases hfiber with ⟨Fbase, hFsize, hFsolv, hFmin⟩
  let F : HypercubeVertex m → Pebbling (HypercubeVertex a) :=
    fun z => if E z = 0 then (fun _ : HypercubeVertex a => 0) else Fbase
  let Dprod : Pebbling (HypercubeVertex a × HypercubeVertex m) :=
    Pebbling.fibersDistribution F
  let D : Pebbling (HypercubeVertex (a + m)) :=
    (splitGraphIso a m).symm.mapDistribution Dprod
  have hpile_le : ∀ z : HypercubeVertex m, E z ≤ costBound := by
    intro z
    exact (Pebbling.le_size E z).trans hEsize
  have hFsolv : ∀ z : HypercubeVertex m,
      Pebbling.SolvableAtLeast (graph a) (F z) (E z) := by
    intro z
    by_cases hz : E z = 0
    · simp [F, hz, Pebbling.solvableAtLeast_zero]
    · simpa [F, hz] using
        Pebbling.solvableAtLeast_mono (hpile_le z) hFsolv
  have hprod_solvable :
      Pebbling.Solvable
        (Graph.cartesianProduct (graph a) (graph m)) Dprod := by
    exact Pebbling.solvable_product_of_fiber_demands
      (G := graph a) (H := graph m)
      (Pebbling.solvable_of_solvableAtLeast hTbase hEsolv) hFsolv
  have hDsolv : Pebbling.Solvable (graph (a + m)) D := by
    exact (splitGraphIso a m).symm.map_solvableAtLeast hprod_solvable
  have hFsize_each : ∀ z : HypercubeVertex m,
      Pebbling.size (F z) ≤ if E z = 0 then 0 else S * K := by
    intro z
    by_cases hz : E z = 0
    · simp [F, hz]
    · simpa [F, hz] using hFsize
  have hprod_size :
      Pebbling.size Dprod ≤
        ∑ z : HypercubeVertex m, if E z = 0 then 0 else S * K := by
    exact Pebbling.size_fibersDistribution_le hFsize_each
  have hsum :
      (∑ z : HypercubeVertex m, if E z = 0 then 0 else S * K) =
        Pebbling.supportSize E * (S * K) := by
    exact Pebbling.sum_ite_nonzero_const E (S * K)
  have hcompressed :
      Pebbling.supportSize E * (S * K) ≤ costBound * K :=
    (Pebbling.supportSize_mul_minPileCost_le_size_mul hEmin).trans
      (Nat.mul_le_mul_right K hEsize)
  have hDsize : Pebbling.size D ≤ costBound * K := by
    calc
      Pebbling.size D = Pebbling.size Dprod := by
        exact (splitGraphIso a m).symm.size_mapDistribution Dprod
      _ ≤ ∑ z : HypercubeVertex m, if E z = 0 then 0 else S * K := hprod_size
      _ = Pebbling.supportSize E * (S * K) := hsum
      _ ≤ costBound * K := hcompressed
  have hprod_min : Pebbling.MinOccupiedPileSize Dprod Snew := by
    intro p hp
    rcases p with ⟨x, z⟩
    by_cases hz : E z = 0
    · simp [Dprod, F, hz] at hp
    · have hpF : Fbase x ≠ 0 := by
        simpa [Dprod, F, Pebbling.fibersDistribution, hz] using hp
      exact (by
        simpa [Dprod, F, Pebbling.fibersDistribution, hz] using hFmin x hpF)
  have hDmin : Pebbling.MinOccupiedPileSize D Snew := by
    exact (splitGraphIso a m).symm.map_minOccupiedPileSize hprod_min
  exact ⟨D, hDsize, hDsolv, hDmin⟩
end PebblingLean.Hypercube

-- Prove2me | solution 1 for PebblingLean.Hypercube.sum_centerSample_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:04:12.579132+00:00
-- url     : https://prove2.me/submissions/a5ae9150-6c4c-44ad-acd0-c2ba6e8f575f

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
public import Theorems.Thm_PebblingLean_Hypercube_card_vertex
public import Theorems.Thm_PebblingLean_Hypercube_fromDiffSet_empty
public import Theorems.Thm_PebblingLean_Hypercube_mem_annulus
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_self
public import Theorems.Thm_PebblingLean_Pebbling_size_single
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_left
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_right
attribute [local simp] PebblingLean.Graph.Walk.length_append
attribute [local simp] PebblingLean.Graph.Walk.length_reverse
attribute [local simp] PebblingLean.Hypercube.fromDiffSet_empty
attribute [local simp] PebblingLean.Hypercube.mem_annulus
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.single_apply_ne
attribute [local simp] PebblingLean.Pebbling.single_apply_self
attribute [local simp] PebblingLean.Pebbling.size_single
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_left
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_ne
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_right



set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution {n N : ℕ} (j : Fin N)
    (f : HypercubeVertex n → ℕ) :
    (∑ sample : CenterSample n N, (f (sample j) : ℚ)) =
      ((2 ^ n) ^ (N - 1) : ℚ) *
        ∑ center : HypercubeVertex n, (f center : ℚ) := by
  classical
  have hfiber :=
    (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (CenterSample n N)))
      (t := (Finset.univ : Finset (HypercubeVertex n)))
      (g := fun sample : CenterSample n N => sample j)
      (fun sample _hsample => Finset.mem_univ (sample j))
      (fun sample : CenterSample n N => (f (sample j) : ℚ)))
  have hinner :
      ∀ center : HypercubeVertex n,
        (∑ sample ∈ (Finset.univ : Finset (CenterSample n N)) with sample j = center,
          (f (sample j) : ℚ)) =
        ((2 ^ n) ^ (N - 1) : ℚ) * (f center : ℚ) := by
    intro center
    let fiber : Finset (CenterSample n N) :=
      (Finset.univ : Finset (CenterSample n N)).filter fun sample => sample j = center
    have hcard : fiber.card = (2 ^ n) ^ (N - 1) := by
      have hpi :=
        Fintype.card_filter_piFinset_const_eq_of_mem
          (s := (Finset.univ : Finset (HypercubeVertex n))) j
          (x := center) (Finset.mem_univ center)
      simpa [fiber, CenterSample, card_vertex] using hpi
    have hconst :
        ∀ sample ∈ fiber, (f (sample j) : ℚ) = (f center : ℚ) := by
      intro sample hsample
      have hsample_eq : sample j = center := by
        simpa [fiber] using (Finset.mem_filter.mp hsample).2
      simp [hsample_eq]
    calc
      (∑ sample ∈ (Finset.univ : Finset (CenterSample n N)) with sample j = center,
          (f (sample j) : ℚ))
          = ∑ sample ∈ fiber, (f (sample j) : ℚ) := by
            rfl
      _ = ∑ _sample ∈ fiber, (f center : ℚ) := by
            exact Finset.sum_congr rfl hconst
      _ = ((2 ^ n) ^ (N - 1) : ℚ) * (f center : ℚ) := by
            simp [Finset.sum_const, hcard, nsmul_eq_mul]
  calc
    (∑ sample : CenterSample n N, (f (sample j) : ℚ))
        = ∑ sample ∈ (Finset.univ : Finset (CenterSample n N)), (f (sample j) : ℚ) := by
          rfl
    _ = ∑ center ∈ (Finset.univ : Finset (HypercubeVertex n)),
        ∑ sample ∈ (Finset.univ : Finset (CenterSample n N)) with sample j = center,
          (f (sample j) : ℚ) := by
          exact hfiber.symm
    _ = ∑ center ∈ (Finset.univ : Finset (HypercubeVertex n)),
        ((2 ^ n) ^ (N - 1) : ℚ) * (f center : ℚ) := by
          exact Finset.sum_congr rfl fun center _hcenter => hinner center
    _ = ((2 ^ n) ^ (N - 1) : ℚ) *
        ∑ center ∈ (Finset.univ : Finset (HypercubeVertex n)), (f center : ℚ) := by
          rw [Finset.mul_sum]
    _ = ((2 ^ n) ^ (N - 1) : ℚ) *
        ∑ center : HypercubeVertex n, (f center : ℚ) := by
          rfl
end PebblingLean.Hypercube

-- Prove2me | solution 1 for SoficGroups.exists_finite_group_embedding_of_expanding_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/ff7f6744-6a84-469b-8807-b68547321462

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_almostCentralizerGap_of_expansion
import Theorems.Thm_SoficGroups_almostCentralizerCluster_eq_iff

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {G : Type*} [Group G] (F : Finset G)
    (M : ExpandingCentralizerFiniteModel G F) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (f : G → H),
      Set.InjOn f (F : Set G) ∧ f 1 = 1 ∧
        ∀ x ∈ F, ∀ y ∈ F, f (x * y) = f x * f y := by
  let hgap : AlmostCentralizerGap M.generators M.tolerance :=
    almostCentralizerGap_of_expansion M.generators M.tolerance M.cheeger
      M.cheeger_positive M.expansion M.small
  let H := AlmostCentralizerClusters M.generators M.tolerance hgap
  letI : Group H := almostCentralizerClusterGroup hgap M.repair
  letI : Finite H := inferInstance
  let f : G → H := fun x => almostCentralizerCluster hgap (M.approximation x)
  refine ⟨H, inferInstance, inferInstance, f, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    by_contra hne
    have hclose :
        5 * permutationDistance
          (M.approximation x).permutation
          (M.approximation y).permutation ≤ Fintype.card M.vertices :=
      (almostCentralizerCluster_eq_iff hgap
        (M.approximation x) (M.approximation y)).mp hxy
    have hfar := M.separated x hx y hy hne
    omega
  · change almostCentralizerCluster hgap (M.approximation 1) =
      almostCentralizerCluster hgap
        (almostCentralizerOne M.generators M.tolerance)
    apply Quotient.sound
    change 5 * permutationDistance (M.approximation 1).permutation 1 ≤
      Fintype.card M.vertices
    simp [M.map_one]
  · intro x hx y hy
    change almostCentralizerCluster hgap (M.approximation (x * y)) =
      almostCentralizerCluster hgap
        (correctedAlmostCentralizerProduct M.repair
          (M.approximation x) (M.approximation y))
    apply Quotient.sound
    let a := M.approximation (x * y)
    let b := correctedAlmostCentralizerProduct M.repair
      (M.approximation x) (M.approximation y)
    change 5 * permutationDistance a.permutation b.permutation ≤
      Fintype.card M.vertices
    rcases hgap.dichotomy a b with hclose | hfar
    · exact hclose
    · have hmul := M.multiplicative x hx y hy
      have hrepair := M.repair.corrected_distance
        (M.approximation x) (M.approximation y)
      have htri := permutationDistance_triangle a.permutation
        ((M.approximation x).permutation *
          (M.approximation y).permutation) b.permutation
      have hsym :
          permutationDistance
            ((M.approximation x).permutation *
              (M.approximation y).permutation) b.permutation =
            permutationDistance b.permutation
              ((M.approximation x).permutation *
                (M.approximation y).permutation) :=
        permutationDistance_comm _ _
      change 4 * Fintype.card M.vertices <
        5 * permutationDistance a.permutation b.permutation at hfar
      change 5 * permutationDistance a.permutation
        ((M.approximation x).permutation *
          (M.approximation y).permutation) ≤ Fintype.card M.vertices at hmul
      change 5 * permutationDistance b.permutation
        ((M.approximation x).permutation *
          (M.approximation y).permutation) ≤
            Fintype.card M.vertices at hrepair
      omega
end SoficGroups

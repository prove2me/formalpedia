-- Prove2me | solution 1 for SoficGroups.SourceRetainedActualMatching.retained_transport_component_matching_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/0e590671-7916-4e01-9090-4c3a8a4db359

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceCompressionMatching_transported_maximumOverlapPart_card_lt_exp_mul
import Theorems.Thm_SoficGroups_SourceCompressionMatching_symmDiff_card_lt_of_overlap_and_exp_card
import Theorems.Thm_SoficGroups_SourceCompressionMatching_target_majority_of_overlap_and_exp_card
import Theorems.Thm_SoficGroups_SourceCompressionRetainedDiscard_retainedComponents_spec

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceRetainedActualMatching
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.SourceRetainedActualMatching
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V)
    (H r eta : ℝ) (hH : 0 < H)
    (C : Finset V)
    (hC : C ∈ retainedTransportedComponents Q T H r eta) :
    SoficGroups.maximumOverlapPart Q C ∈ Q.parts ∧
      (1 - eta) * (C.card : ℝ) ≤
        ((C ∩ SoficGroups.maximumOverlapPart Q C).card : ℝ) ∧
      ((C ∆ SoficGroups.maximumOverlapPart Q C).card : ℝ) <
        (Real.exp H - 1 + 2 * eta) * (C.card : ℝ) ∧
      (2 * (Real.exp H - 1 + 2 * eta) < 1 →
        (SoficGroups.maximumOverlapPart Q C).card <
          2 * (C ∩ SoficGroups.maximumOverlapPart Q C).card) := by
  classical
  have hret :
      C ∈ SoficGroups.SourceCompressionRetainedDiscard.retainedComponents
        (SoficGroups.transportedUnivFinpartition Q T) Q T
        (logarithmicComponentRank Q H r) eta := by
    exact hC
  obtain ⟨hpart, htarget, hoverlap, y, hy, hrank⟩ :=
    SoficGroups.SourceCompressionRetainedDiscard.retainedComponents_spec
      (SoficGroups.transportedUnivFinpartition Q T) Q T
      (logarithmicComponentRank Q H r) eta C hret
  have hpartImage := hpart
  rw [SoficGroups.transportedUnivFinpartition_parts] at hpartImage
  obtain ⟨C₀, hC₀, hmap⟩ := Finset.mem_image.mp hpartImage
  have hyMap : y ∈ C₀.map T.toEmbedding := by
    rw [hmap]
    exact (Finset.mem_inter.mp hy).1
  obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hyMap
  have hxy' : T x = y := hxy
  have hTx :
      T x ∈ SoficGroups.maximumOverlapPart Q
        (C₀.map T.toEmbedding) := by
    rw [hmap]
    simpa only [hxy'] using (Finset.mem_inter.mp hy).2
  have hfloor :
      SoficGroups.MidrankPermutationEnergy.offsetFloorRank
        (fun z : V =>
          Real.log (SoficGroups.partitionComponentSize Q z : ℝ))
        H r (T x) =
      SoficGroups.MidrankPermutationEnergy.offsetFloorRank
        (fun z : V =>
          Real.log (SoficGroups.partitionComponentSize Q z : ℝ))
        H r x := by
    have heq :
        logarithmicComponentRank Q H r (T x) =
          logarithmicComponentRank Q H r x := by
      calc
        logarithmicComponentRank Q H r (T x) =
            logarithmicComponentRank Q H r y :=
          congrArg (logarithmicComponentRank Q H r) hxy'
        _ = logarithmicComponentRank Q H r (T.symm y) :=
          hrank.symm
        _ = logarithmicComponentRank Q H r x := by
          rw [← hxy', Equiv.symm_apply_apply]
    exact heq
  have hsize :=
    SoficGroups.SourceCompressionMatching.transported_maximumOverlapPart_card_lt_exp_mul
      Q T C₀ hC₀ H r hH x hx hTx hfloor
  rw [hmap] at hsize
  have hcard : C.card = C₀.card := by
    rw [← hmap, Finset.card_map]
  rw [← hcard] at hsize
  have hsymmetric :=
    SoficGroups.SourceCompressionMatching.symmDiff_card_lt_of_overlap_and_exp_card
      C (SoficGroups.maximumOverlapPart Q C) H eta
      hoverlap hsize
  refine ⟨htarget, hoverlap, hsymmetric, ?_⟩
  intro hsmall
  exact
    SoficGroups.SourceCompressionMatching.target_majority_of_overlap_and_exp_card
      C (SoficGroups.maximumOverlapPart Q C)
      ((SoficGroups.transportedUnivFinpartition Q T).nonempty_of_mem_parts hpart)
      H eta hoverlap hsize hsmall
end SoficGroups.SourceRetainedActualMatching

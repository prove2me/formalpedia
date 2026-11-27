-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HausdorffNullComplementConnected_proof_512a6d2e78cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:57:34.352058+00:00
-- url     : https://prove2.me/submissions/20eeee28-f0e4-4206-86b4-785d2b6132f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHausdorffNullComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHausdorffNullComplementConnected
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_diff_nonempty_of_hausdorffMeasure_null_3e3c98cc7708
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_convex_diff_isPreconnected_6dbd81d3253b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Metric MeasureTheory Set Relation
open scoped NNReal ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace HausdorffNullComplementConnected
theorem _root_.solution : HausdorffNullComplementConnected.Statement := by
  intro E _ _ _ _ _ D C hDo hDc hC
  by_cases h0 : Module.finrank ℝ E = 0
  · have : Subsingleton E := Module.finrank_zero_iff.1 h0
    exact Set.subsingleton_of_subsingleton.isPreconnected
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero h0
  have hC' : μH[(k : ℝ)] C = 0 := by
    rw [hk, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hC
    exact hC
  choose! r hr0 hrD using Metric.isOpen_iff.1 hDo
  have hU : D \ C = ⋃ z ∈ D, ball z (r z) \ C := by
    ext z
    simp only [mem_sdiff, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hz, hzC⟩
      exact ⟨z, hz, mem_ball_self (hr0 z hz), hzC⟩
    · rintro ⟨w, hw, hzb, hzC⟩
      exact ⟨hrD w hw hzb, hzC⟩
  rw [hU]
  refine IsPreconnected.biUnion_of_reflTransGen
    (fun z _ => convex_diff_isPreconnected hk hC' isOpen_ball (convex_ball z (r z))) ?_
  intro z hz w hw
  refine hDc.induction₂' (fun a b => ReflTransGen
      (fun i j => ((ball i (r i) \ C) ∩ (ball j (r j) \ C)).Nonempty ∧ i ∈ D) a b) ?_
    (fun a b c _ _ _ h1 h2 => h1.trans h2) hz hw
  intro a ha
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a (hr0 a ha)), self_mem_nhdsWithin]
    with b hb hbD
  obtain ⟨p, ⟨hpa, hpb⟩, hpC⟩ := diff_nonempty_of_hausdorffMeasure_null hk hC'
    (isOpen_ball.inter isOpen_ball) ⟨b, hb, mem_ball_self (hr0 b hbD)⟩
  exact ⟨ReflTransGen.single ⟨⟨p, ⟨hpa, hpC⟩, hpb, hpC⟩, ha⟩,
    ReflTransGen.single ⟨⟨p, ⟨hpb, hpC⟩, hpa, hpC⟩, hbD⟩⟩
end HausdorffNullComplementConnected
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

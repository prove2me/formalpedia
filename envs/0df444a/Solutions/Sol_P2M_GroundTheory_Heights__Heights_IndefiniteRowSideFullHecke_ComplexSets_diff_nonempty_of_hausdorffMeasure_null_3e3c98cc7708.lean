-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_diff_nonempty_of_hausdorffMeasure_null_3e3c98cc7708
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:32:10.974263+00:00
-- url     : https://prove2.me/submissions/5b88c7e9-4073-4bdf-bdbf-7ddd92f363c7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHausdorffNullComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHausdorffNullComplementConnected

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
theorem _root_.solution [FiniteDimensional ℝ E] {k : ℕ}
    (hk : Module.finrank ℝ E = k + 1) {C : Set E} (hC : μH[(k : ℝ)] C = 0) {U : Set E}
    (hU : IsOpen U) (hne : U.Nonempty) : (U \ C).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at h
  obtain ⟨z, hz⟩ := hne
  have hlt : ((k : ℝ≥0) : ℝ≥0∞) < dimH U := by
    rw [Real.dimH_of_mem_nhds (hU.mem_nhds hz), hk]
    exact_mod_cast Nat.lt_succ_self k
  have htop := hausdorffMeasure_of_lt_dimH hlt
  rw [NNReal.coe_natCast, measure_mono_null h hC] at htop
  exact ENNReal.zero_ne_top htop
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

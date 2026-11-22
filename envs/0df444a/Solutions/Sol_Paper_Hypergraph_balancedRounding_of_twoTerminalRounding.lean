-- Prove2me | solution 1 for Paper.Hypergraph.balancedRounding_of_twoTerminalRounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:34:59.458814+00:00
-- url     : https://prove2.me/submissions/3f926c7a-44d8-423c-ba6b-0e5dd912c58b

import Definitions.Def_Paper_RoundingRecursion
import Definitions.Def_Paper_TwoTerminalRounding
import Definitions.Def_Paper_BalancedRounding
import Theorems.Thm_Paper_Hypergraph_rounding_volume_factor_le
import Theorems.Thm_Paper_Hypergraph_nontrivial_rounding_cover_lower_bound
import Theorems.Thm_Paper_Hypergraph_rounding_coefficient_identity
import Theorems.Thm_Paper_Hypergraph_cutoff_from_rounding
import Theorems.Thm_Paper_Hypergraph_cutoff_recursion
import Theorems.Thm_Paper_Hypergraph_demand_lt_threshold_of_mem_compl
import Theorems.Thm_Paper_Hypergraph_restrictDemand_cost_le
import Theorems.Thm_Paper_Hypergraph_roundingThreshold_cost_le
import Theorems.Thm_Paper_Hypergraph_roundingThreshold_subset_support
import Theorems.Thm_Paper_Hypergraph_setCoverCost_union_le
import Theorems.Thm_Paper_Hypergraph_twoTerminalFactor_nonneg
import Theorems.Thm_Paper_Hypergraph_twoTerminalRounding_induced


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (round : TwoTerminalRounding) : BalancedRounding := by
  intro H γ x φ hφ hγ hx hnontrivial
  have hγ0 : ∀ e ∈ H.edges, 0 ≤ γ e := fun e he => (hγ e he).1
  have hn : ∀ v ∈ H.vertices, 0 ≤ x v := fun v hv => (hx.1 v hv).1
  let r := (1 - φ) / 2
  let L := Real.logb 2 (H.coverCost x / r)
  let t := (18 + 4 * L) / r
  let a := t⁻¹
  let R := H.vertices.filter (fun v => x v ≠ 0)
  let C := H.twoTerminalFactor R
  let S₀ := H.roundingThreshold x a
  let Q := H.vertices \ S₀
  have hr : 0 < r ∧ r < 1 := by dsimp [r]; constructor <;> linarith
  have hK : r / 2 ≤ H.coverCost x := by
    have h := H.nontrivial_rounding_cover_lower_bound hφ hγ0 hx hnontrivial
    dsimp [r]
    linarith
  have hKpos : 0 < H.coverCost x := by linarith [hr.1]
  have hL : -1 ≤ L := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (div_pos hKpos hr.1)).2
    norm_num
    exact (le_div_iff₀ hr.1).2 (by linarith)
  have ht : 0 < t := div_pos (by linarith) hr.1
  have ha : 0 < a := inv_pos.mpr ht
  have hC : 0 ≤ C := H.twoTerminalFactor_nonneg R
  have hthreshold : a = (r / (9 + 2 * L)) / 2 := by
    dsimp [a, t]
    rw [inv_div, show 18 + 4 * L = (9 + 2 * L) * 2 by ring]
    exact (div_div r (9 + 2 * L) 2).symm
  have hcut : ∀ U ⊆ Q, U.Nonempty → Nonempty
      (H.CutoffPiece γ x U (φ / (1 - r) * ∑ e ∈ H.edges, γ e) (C * t)) := by
    intro U hU hne
    apply H.cutoff_from_rounding hγ0 hx hr hC hK (hU.trans sdiff_subset) hne
    · intro v hv
      have h := H.demand_lt_threshold_of_mem_compl x a (hU hv)
      rwa [hthreshold] at h
    · exact fun A B z hA hB hz hsupp => twoTerminalRounding_induced round H U x A B z hA hB hz hsupp
  obtain ⟨S, hSQ, hSR, hbal, hcost⟩ := H.cutoff_recursion hγ0 hn (mul_nonneg hC ht.le)
    Q sdiff_subset hcut
  refine ⟨S₀ ∪ S, union_subset (H.roundingThreshold_subset_support x ha) hSR, ?_, ?_⟩
  · refine ⟨union_subset (filter_subset _ _) (hSQ.trans sdiff_subset), ?_⟩
    intro K hKcomp
    have hset : H.vertices \ (S₀ ∪ S) = Q \ S := by
      ext v
      simp [Q]
      tauto
    rw [hset] at hKcomp
    change H.edgeVolume γ K ≤ _
    exact (hbal K hKcomp).trans
      (mul_le_mul_of_nonneg_right (rounding_volume_factor_le hφ) (sum_nonneg hγ0))
  · have hcost' : H.setCoverCost S ≤ C * t * H.coverCost x :=
      hcost.trans (mul_le_mul_of_nonneg_left (H.restrictDemand_cost_le hn Q) (mul_nonneg hC ht.le))
    have hcost₀ : H.setCoverCost S₀ ≤ t * H.coverCost x := by
      simpa [a] using H.roundingThreshold_cost_le hn ha
    have hfinal : H.setCoverCost (S₀ ∪ S) ≤ (C + 1) * t * H.coverCost x := by
      calc
        _ ≤ H.setCoverCost S₀ + H.setCoverCost S := H.setCoverCost_union_le _ _
        _ ≤ t * H.coverCost x + C * t * H.coverCost x := add_le_add hcost₀ hcost'
        _ = _ := by ring
    have ht_eq := rounding_coefficient_identity hKpos hφ.2
    change t = _ at ht_eq
    simpa only [ht_eq, C, R, twoTerminalFactor] using hfinal
end Paper.Hypergraph

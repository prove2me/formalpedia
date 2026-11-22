-- Prove2me | solution 1 for Paper.Hypergraph.manuscript_balanced_separator_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:37:07.810083+00:00
-- url     : https://prove2.me/submissions/35d47834-4676-4bc4-86be-575fec53dc1f

import Definitions.Def_Paper_RoundingIndependence
import Definitions.Def_Paper_RoundingDegeneracy
import Definitions.Def_Paper_BalancedRounding
import Definitions.Def_Paper_RoundingComplete
import Theorems.Thm_Paper_Hypergraph_balanced_rounding
import Theorems.Thm_Paper_Hypergraph_manuscript_rounding_cost_bound
import Theorems.Thm_Paper_Hypergraph_manuscript_rounding_structural_bounds
import Theorems.Thm_Paper_Hypergraph_log_nat_nonneg


set_option autoImplicit true
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution : ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (H : Hypergraph) (γ x : ℕ → ℝ), H.EdgeWeight γ →
    H.FractionalBalanced γ (1 / 2) x →
    ∃ S ⊆ H.vertices, H.IntegralBalanced γ (5 / 6) S ∧
      H.setCoverCost S ≤ C₀ * (H.degeneracy : ℝ) * H.coverCost x *
        (Real.log (max 2 (H.coverCost x)) / Real.log 2) ∧
      H.setCoverCost S ≤ C₀ *
        max 1 (Real.log (H.independenceNumber : ℝ) / Real.log 2) * H.coverCost x *
        (Real.log (max 2 (H.coverCost x)) / Real.log 2) := by
  refine ⟨1560, by norm_num, ?_⟩
  intro H γ x hγ hx
  let q := H.coverCost x
  let L := Real.log (max 2 q) / Real.log 2
  have hq : 0 ≤ q := H.coverCost_nonneg x
  have hL : 0 ≤ L := by
    apply div_nonneg
    · exact Real.log_nonneg (by linarith [le_max_left (2 : ℝ) q])
    · exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  by_cases hempty : H.IntegralBalanced γ (5 / 6) ∅
  · refine ⟨∅, empty_subset _, hempty, ?_, ?_⟩ <;>
      rw [show H.setCoverCost ∅ = 0 from H.coverCost_eq_zero_of_nonpos (by simp [indicator])]
    · change 0 ≤ 1560 * (H.degeneracy : ℝ) * q * L
      positivity
    · change 0 ≤ 1560 * max 1 _ * q * L
      positivity
  · have hne : H.vertices.Nonempty := by
      have he : H.edges.Nonempty := by
        by_contra h
        have hz := not_nonempty_iff_eq_empty.mp h
        have := hγ.2
        simp [hz] at this
      obtain ⟨e, he⟩ := he
      obtain ⟨v, hv⟩ := H.edge_nonempty e he
      exact ⟨v, H.edge_subset e he hv⟩
    have hn : ¬ H.IntegralBalanced γ
        ((1 + 3 * (1 / 2 : ℝ)) / (2 + 2 * (1 / 2 : ℝ))) ∅ := by
      norm_num
      exact hempty
    obtain ⟨S, hS, hbal, hcost⟩ := balanced_rounding H γ x (1 / 2)
      (by norm_num) hγ.1 hx hn
    let T := H.vertices.filter (fun v => x v ≠ 0)
    let A := min (8 + 4 * Real.log ((H.induce T).independenceNumber : ℝ))
      (6 * (H.degeneracy : ℝ)) + 1
    have hA : 0 ≤ A := by
      have := log_nat_nonneg (H.induce T).independenceNumber
      dsimp [A]
      positivity
    have hsharp : H.setCoverCost S ≤ A * (120 * q * L) := by
      calc
        _ ≤ _ := hcost
        _ = A * (((44 + 8 * (Real.log (q / (1 - (1 / 2 : ℝ))) / Real.log 2)) /
            (1 - (1 / 2 : ℝ))) * q) := by dsimp [A, T, q]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (manuscript_rounding_cost_bound hq) hA
    obtain ⟨hd, ha⟩ := H.manuscript_rounding_structural_bounds hne T
    have hd' : A ≤ 13 * (H.degeneracy : ℝ) := by
      dsimp [A]
      linarith [Nat.cast_nonneg (α := ℝ) H.degeneracy]
    refine ⟨S, hS.trans (filter_subset _ _), by norm_num at hbal; exact hbal, ?_, ?_⟩
    · calc
        _ ≤ A * (120 * q * L) := hsharp
        _ ≤ (13 * (H.degeneracy : ℝ)) * (120 * q * L) :=
          mul_le_mul_of_nonneg_right hd' (by positivity)
        _ = _ := by dsimp [q, L]; ring
    · calc
        _ ≤ A * (120 * q * L) := hsharp
        _ ≤ (13 * max 1 (Real.log (H.independenceNumber : ℝ) / Real.log 2)) *
            (120 * q * L) := mul_le_mul_of_nonneg_right ha (by positivity)
        _ = _ := by dsimp [q, L]; ring
end Paper.Hypergraph

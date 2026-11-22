-- Prove2me | solution 1 for Paper.Hypergraph.balanced_separator_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:12.397348+00:00
-- url     : https://prove2.me/submissions/638a2e12-b919-4fbc-9b29-d3f6fc8adb08

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_rounding_structural_bound
import Theorems.Thm_Paper_Hypergraph_rounding_cost_bound

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (rounding : BalancedRounding) : ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (H : Hypergraph) (γ x : ℕ → ℝ), H.EdgeWeight γ →
    H.FractionalBalanced γ (1 / 2) x →
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0), H.IntegralBalanced γ (5 / 6) S ∧
      H.setCoverCost S ≤ C₀ *
        (1 + min (H.degeneracy : ℝ)
          (Real.log (2 + ((H.induce (H.vertices.filter (fun v => x v ≠ 0))).independenceNumber : ℝ)))) *
        (H.coverCost x + 1) * Real.log (2 + H.coverCost x) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨9 * (120 / Real.log 2), by positivity, ?_⟩
  intro H γ x hγ hx
  let a := (H.induce (H.vertices.filter (fun v => x v ≠ 0))).independenceNumber
  let d := H.degeneracy
  let q := H.coverCost x
  have hq : 0 ≤ q := H.coverCost_nonneg x
  have hl : 0 ≤ Real.log (2 + q) := Real.log_nonneg (by linarith)
  have hfactor : 0 ≤ 1 + min (d : ℝ) (Real.log (2 + (a : ℝ))) := by
    have : 0 ≤ Real.log (2 + (a : ℝ)) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) a; linarith)
    positivity
  by_cases hempty : H.IntegralBalanced γ (5 / 6) ∅
  · refine ⟨∅, empty_subset _, hempty, ?_⟩
    have hc : H.setCoverCost ∅ ≤ 0 := by
      have hh : H.Cover (indicator ∅) (fun _ => 0) := by
        constructor
        · intros; norm_num
        · intros; simp [indicator]
      simpa [setCoverCost] using H.coverCost_le hh
    apply hc.trans
    change 0 ≤ (9 * (120 / Real.log 2)) *
      (1 + min (d : ℝ) (Real.log (2 + (a : ℝ)))) * (q + 1) * Real.log (2 + q)
    positivity
  · have hn : ¬ H.IntegralBalanced γ
        ((1 + 3 * (1 / 2 : ℝ)) / (2 + 2 * (1 / 2 : ℝ))) ∅ := by
      norm_num
      exact hempty
    obtain ⟨S, hS, hbal, hcost⟩ := rounding H γ x (1 / 2)
      (by norm_num) hγ.1 hx hn
    refine ⟨S, hS, by norm_num at hbal; exact hbal, ?_⟩
    have ha : 0 ≤ Real.log (a : ℝ) := by
      by_cases ha0 : a = 0
      · simp [ha0]
      · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha0)
    have hA : 0 ≤ min (8 + 4 * Real.log (a : ℝ)) (6 * (d : ℝ)) + 1 := by
      positivity
    have hB : 0 ≤ (120 / Real.log 2) * (q + 1) * Real.log (2 + q) := by positivity
    calc
      H.setCoverCost S ≤ _ := hcost
      _ = (min (8 + 4 * Real.log (a : ℝ)) (6 * (d : ℝ)) + 1) *
          (((44 + 8 * (Real.log (q / (1 - (1 / 2 : ℝ))) / Real.log 2)) /
            (1 - (1 / 2 : ℝ))) * q) := by dsimp [a, d, q]; ring
      _ ≤ (min (8 + 4 * Real.log (a : ℝ)) (6 * (d : ℝ)) + 1) *
          ((120 / Real.log 2) * (q + 1) * Real.log (2 + q)) :=
        mul_le_mul_of_nonneg_left (rounding_cost_bound hq) hA
      _ ≤ (9 * (1 + min (d : ℝ) (Real.log (2 + (a : ℝ))))) *
          ((120 / Real.log 2) * (q + 1) * Real.log (2 + q)) :=
        mul_le_mul_of_nonneg_right (rounding_structural_bound d a) hB
      _ = _ := by dsimp [a, d, q]; ring
end Paper.Hypergraph

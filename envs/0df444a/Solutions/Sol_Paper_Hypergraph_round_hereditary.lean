-- Prove2me | solution 1 for Paper.Hypergraph.round_hereditary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:58.134558+00:00
-- url     : https://prove2.me/submissions/c01fd10d-2388-4bd4-9488-c84d1a3f67d3

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_structure_hereditary
import Theorems.Thm_Paper_Hypergraph_full_fractional_separator
import Theorems.Thm_Paper_Hypergraph_beta_bounds
import Theorems.Thm_Paper_Hypergraph_beta_le_fsep
import Theorems.Thm_Paper_Hypergraph_balanced_separator_rounding
import Theorems.Thm_Paper_Hypergraph_width_scale_mono
import Theorems.Thm_Paper_Hypergraph_scale_infimum

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (rounding : BalancedRounding) : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ H : Hypergraph,
    H.Connected → H.sep (5 / 6) ≤ C₁ * H.structuralFactor *
      (H.fsep (1 / 2) + 1) * Real.log (2 + H.fsep (1 / 2)) := by
  obtain ⟨C₀, hC₀, hround⟩ := balanced_separator_rounding rounding
  refine ⟨C₀, hC₀, ?_⟩
  intro H _hH
  have hf0 : 0 ≤ H.fsep (1 / 2) := Real.sSup_nonneg' ⟨0, Set.mem_insert _ _, le_rfl⟩
  have hl0 : 0 ≤ H.structuralFactor := by
    apply add_nonneg zero_le_one
    exact le_min (Nat.cast_nonneg _) (Real.log_nonneg (by
      have := Nat.cast_nonneg (α := ℝ) H.independenceNumber; linarith))
  have hcoeff : 0 ≤ C₀ * H.structuralFactor := mul_nonneg hC₀.le hl0
  have hlog0 : 0 ≤ Real.log (2 + H.fsep (1 / 2)) := Real.log_nonneg (by linarith)
  refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
  rintro r (rfl | ⟨W, hW, γ, hγ, rfl⟩)
  · positivity
  · let J := H.induce W
    let A : Set ℝ := {r | ∃ x, J.FractionalBalanced γ (1 / 2) x ∧ r = J.coverCost x}
    have hfull := J.full_fractional_separator hγ (θ := 1 / 2) (by norm_num)
    have hne : A.Nonempty := ⟨_, indicator J.vertices, hfull.1, rfl⟩
    have hA : ∀ a ∈ A, 0 ≤ a := by
      rintro a ⟨x, hx, rfl⟩
      exact J.coverCost_nonneg x
    have hinst : J.integralOptimum (5 / 6) γ ≤
        C₀ * H.structuralFactor * (J.beta (1 / 2) γ + 1) * Real.log (2 + J.beta (1 / 2) γ) := by
      change _ ≤ (C₀ * H.structuralFactor) * (sInf A + 1) * Real.log (2 + sInf A)
      rw [scale_infimum hne hA hcoeff]
      refine le_csInf (hne.image _) ?_
      rintro r ⟨a, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨S, hS, hbal, hcost⟩ := hround J γ x hγ hx
      have hopt : J.integralOptimum (5 / 6) γ ≤ J.setCoverCost S := by
        refine csInf_le ⟨0, ?_⟩ ⟨S, hbal, rfl⟩
        rintro r ⟨T, hT, rfl⟩
        exact J.coverCost_nonneg (indicator T)
      have hdeg : (J.degeneracy : ℝ) ≤ H.degeneracy := by
        exact_mod_cast (H.structure_hereditary W).1
      have halpha : (J.induce (J.vertices.filter (fun v => x v ≠ 0))).independenceNumber ≤
          H.independenceNumber :=
        (J.structure_hereditary _).2.trans (H.structure_hereditary W).2
      have hfactor : 1 + min (J.degeneracy : ℝ)
          (Real.log (2 + ((J.induce (J.vertices.filter (fun v => x v ≠ 0))).independenceNumber : ℝ))) ≤
          H.structuralFactor := by
        unfold structuralFactor
        apply add_le_add le_rfl
        apply min_le_min hdeg
        apply Real.log_le_log (by positivity)
        exact_mod_cast (Nat.add_le_add_left halpha 2)
      have hx0 := J.coverCost_nonneg x
      have hxl : 0 ≤ Real.log (2 + J.coverCost x) := Real.log_nonneg (by linarith)
      exact hopt.trans (hcost.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfactor hC₀.le) (by linarith)) hxl))
    apply hinst.trans
    have hb0 := (J.beta_bounds hγ (θ := 1 / 2) (by norm_num)).1
    have hb := H.beta_le_fsep hW hγ (θ := 1 / 2) (by norm_num)
    convert mul_le_mul_of_nonneg_left (width_scale_mono hb0 hb) hcoeff using 1 <;> ring
end Paper.Hypergraph

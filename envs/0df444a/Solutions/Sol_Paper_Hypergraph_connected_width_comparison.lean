-- Prove2me | solution 1 for Paper.Hypergraph.connected_width_comparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:47.387484+00:00
-- url     : https://prove2.me/submissions/14ad98f0-e4fc-43bc-b7dc-611562262ba7

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_elementary_width_bounds
import Theorems.Thm_Paper_Hypergraph_recursive_separator_decomposition
import Theorems.Thm_Paper_Hypergraph_fractional_separators_le_adw
import Theorems.Thm_Paper_Hypergraph_width_scale_mono
import Theorems.Thm_Paper_Hypergraph_round_hereditary

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (rounding : BalancedRounding) : ∃ C : ℝ, 0 < C ∧ ∀ H : Hypergraph,
    H.Connected → H.fhw ≤ C * H.structuralFactor *
      (H.adw + 1) * Real.log (2 + H.adw) := by
  obtain ⟨C₁, hC₁, hround⟩ := round_hereditary rounding
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨7 * (C₁ + (Real.log 2)⁻¹), by positivity, ?_⟩
  intro H hH
  have ha := (H.elementary_width_bounds).1
  have hl : 1 ≤ H.structuralFactor := by
    unfold structuralFactor
    have hn : (0 : ℝ) ≤ H.degeneracy := Nat.cast_nonneg _
    have hlog : 0 ≤ Real.log (2 + (H.independenceNumber : ℝ)) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) H.independenceNumber; linarith)
    have := le_min hn hlog
    linarith
  have hf : 0 ≤ H.fsep (1 / 2) :=
    Real.sSup_nonneg' ⟨0, Set.mem_insert _ _, le_rfl⟩
  have hscale := width_scale_mono hf (H.fractional_separators_le_adw (by norm_num))
  have hs : H.sep (5 / 6) ≤ C₁ * H.structuralFactor *
      ((H.adw + 1) * Real.log (2 + H.adw)) := by
    refine (hround H hH).trans ?_
    convert mul_le_mul_of_nonneg_left hscale (mul_nonneg hC₁.le (by linarith : 0 ≤ H.structuralFactor)) using 1 <;> ring
  have ht : Real.log 2 ≤ H.structuralFactor *
      ((H.adw + 1) * Real.log (2 + H.adw)) := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 + H.adw)
    have hprod : 1 ≤ H.structuralFactor * (H.adw + 1) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ H.structuralFactor) ha]
    calc
      Real.log 2 ≤ Real.log (2 + H.adw) := hlog
      _ ≤ (H.structuralFactor * (H.adw + 1)) * Real.log (2 + H.adw) :=
        le_mul_of_one_le_left (hlog2.le.trans hlog) hprod
      _ = _ := by ring
  have habs : 1 ≤ (Real.log 2)⁻¹ * (H.structuralFactor *
      ((H.adw + 1) * Real.log (2 + H.adw))) := by
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hlog2).mpr (by simpa using ht)
  have hc := H.recursive_separator_decomposition (η := 5 / 6) (by norm_num)
  norm_num at hc
  calc
    H.fhw ≤ 7 * (H.sep (5 / 6) + 1) := hc
    _ ≤ 7 * (C₁ * H.structuralFactor * ((H.adw + 1) * Real.log (2 + H.adw)) +
        (Real.log 2)⁻¹ * (H.structuralFactor * ((H.adw + 1) * Real.log (2 + H.adw)))) := by linarith
    _ = _ := by ring
end Paper.Hypergraph

-- Prove2me | solution 1 for Paper.Hypergraph.structuralFactor_le_lambda
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:27.370923+00:00
-- url     : https://prove2.me/submissions/b51d48df-5634-464e-8627-39f43ffbc488

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_degeneracy_ge_one
import Theorems.Thm_Paper_Hypergraph_independenceNumber_ge_one

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (hne : H.vertices.Nonempty) :
    H.structuralFactor ≤ 4 * H.lambda := by
  have ha : (1 : ℝ) ≤ H.independenceNumber := by
    exact_mod_cast H.independenceNumber_ge_one hne
  have hd : (1 : ℝ) ≤ H.degeneracy := by exact_mod_cast H.degeneracy_ge_one hne
  let L := max 1 (Real.log (H.independenceNumber : ℝ) / Real.log 2)
  have hL : 1 ≤ L := le_max_left _ _
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h3le : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlog : Real.log (H.independenceNumber : ℝ) ≤ L := by
    have hh : Real.log (H.independenceNumber : ℝ) ≤ L * Real.log 2 :=
      (div_le_iff₀ h2).mp (le_max_right _ _)
    have := mul_le_mul_of_nonneg_left h2le (by linarith : 0 ≤ L)
    nlinarith
  have hb : Real.log (2 + (H.independenceNumber : ℝ)) ≤ 3 * L := by
    calc
      _ ≤ Real.log (3 * (H.independenceNumber : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 3 + Real.log (H.independenceNumber : ℝ) :=
        Real.log_mul (by norm_num) (by linarith)
      _ ≤ 3 * L := by linarith
  change 1 + min (H.degeneracy : ℝ) _ ≤ 4 * min (H.degeneracy : ℝ) L
  rcases le_total (H.degeneracy : ℝ) L with h | h
  · rw [min_eq_left h]
    have := min_le_left (H.degeneracy : ℝ) (Real.log (2 + (H.independenceNumber : ℝ)))
    linarith
  · rw [min_eq_right h]
    have := min_le_right (H.degeneracy : ℝ) (Real.log (2 + (H.independenceNumber : ℝ)))
    linarith
end Paper.Hypergraph

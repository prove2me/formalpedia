-- Prove2me | solution 1 for Paper.Hypergraph.manuscript_rounding_structural_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:25.888238+00:00
-- url     : https://prove2.me/submissions/3771f9d6-ac59-4172-a1d3-fa6ec495d803

import Definitions.Def_Paper_RoundingIndependence
import Definitions.Def_Paper_RoundingDegeneracy
import Definitions.Def_Paper_BalancedRounding
import Definitions.Def_Paper_RoundingComplete
import Theorems.Thm_Paper_Hypergraph_degeneracy_ge_one
import Theorems.Thm_Paper_Hypergraph_log_nat_mono
import Theorems.Thm_Paper_Hypergraph_structure_hereditary


set_option autoImplicit true
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph)
    (hne : H.vertices.Nonempty) (T : Finset ℕ) :
    (min (8 + 4 * Real.log ((H.induce T).independenceNumber : ℝ))
      (6 * (H.degeneracy : ℝ)) + 1 ≤ 7 * (H.degeneracy : ℝ)) ∧
    (min (8 + 4 * Real.log ((H.induce T).independenceNumber : ℝ))
      (6 * (H.degeneracy : ℝ)) + 1 ≤
      13 * max 1 (Real.log (H.independenceNumber : ℝ) / Real.log 2)) := by
  have hd : (1 : ℝ) ≤ H.degeneracy := by exact_mod_cast H.degeneracy_ge_one hne
  have hm := log_nat_mono (H.structure_hereditary T).2
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  let L := max 1 (Real.log (H.independenceNumber : ℝ) / Real.log 2)
  have hL : 1 ≤ L := le_max_left _ _
  have hlog : Real.log (H.independenceNumber : ℝ) ≤ L := by
    have hh : Real.log (H.independenceNumber : ℝ) ≤ L * Real.log 2 :=
      (div_le_iff₀ h2).mp (le_max_right _ _)
    have := mul_le_mul_of_nonneg_left h2le (by linarith : 0 ≤ L)
    linarith
  constructor
  · linarith [min_le_right (8 + 4 * Real.log ((H.induce T).independenceNumber : ℝ))
      (6 * (H.degeneracy : ℝ))]
  · change _ ≤ 13 * L
    linarith [min_le_left (8 + 4 * Real.log ((H.induce T).independenceNumber : ℝ))
      (6 * (H.degeneracy : ℝ))]
end Paper.Hypergraph

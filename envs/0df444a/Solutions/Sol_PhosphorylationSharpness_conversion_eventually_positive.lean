-- Prove2me | solution 1 for PhosphorylationSharpness.conversion_eventually_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:31:36.751886+00:00
-- url     : https://prove2.me/submissions/1a8d66d3-0e1d-4e3d-8219-1c9957ac923b

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
import Theorems.Thm_PhosphorylationSharpness_rawD_scaled_limit
import Theorems.Thm_PhosphorylationSharpness_rawB_scaled_limit
import Theorems.Thm_PhosphorylationSharpness_raw_support

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology
namespace PhosphorylationSharpness
theorem _root_.solution {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) :
    ∀ᶠ r : ℝ in atTop, DensePositive (rawD p q r) m ∧ DensePositive (rawB p q r) m := by
  have hd (i : Fin (m+1)) : ∀ᶠ r : ℝ in atTop, 0 < (rawD p q r).coeff i := by
    have hl := rawD_scaled_limit hp hq i
    have hz : 0 < 4*p.coeff m*q.coeff i := by
      exact mul_pos (mul_pos (by norm_num) (hp.1 m le_rfl)) (hq.1 i (by omega))
    filter_upwards [hl.eventually (Ioi_mem_nhds hz), eventually_gt_atTop (0:ℝ)] with r h hr
    exact (div_pos_iff_of_pos_right (pow_pos hr m)).mp h
  have hb (i : Fin (m+1)) : ∀ᶠ r : ℝ in atTop, 0 < (rawB p q r).coeff i := by
    have hl := rawB_scaled_limit hp hq i
    have hz : 0 < 4*p.coeff m*(q.coeff i+p.coeff i) := by
      exact mul_pos (mul_pos (by norm_num) (hp.1 m le_rfl))
        (add_pos (hq.1 i (by omega)) (hp.1 i (by omega)))
    filter_upwards [hl.eventually (Ioi_mem_nhds hz), eventually_gt_atTop (0:ℝ)] with r h hr
    exact (div_pos_iff_of_pos_right (pow_pos hr (m+1))).mp h
  have hdall := Filter.eventually_all.mpr hd
  have hball := Filter.eventually_all.mpr hb
  filter_upwards [hdall, hball] with r hd hb
  constructor
  · exact ⟨fun i hi => hd ⟨i, by omega⟩, fun i hi => (raw_support hp hq r i hi).1⟩
  · exact ⟨fun i hi => hb ⟨i, by omega⟩, fun i hi => (raw_support hp hq r i hi).2⟩
end PhosphorylationSharpness

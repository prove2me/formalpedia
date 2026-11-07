-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.zone_ae_cap_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:42:39.058026+00:00
-- url     : https://prove2.me/submissions/aab41cc3-257c-4392-98a2-b475341d0ef0

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Area
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Zones
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_latitude_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) (a b : ℝ) :
    zone u a b =ᵐ[area] (cap u a \ cap u b : Set Sphere) := by
  have hnot : ∀ᵐ (s : Sphere) ∂area, inner ℝ (u : Space) (s : Space) ≠ b := by
    apply ae_iff.mpr
    simpa only [not_not] using area_latitude_zero u b
  filter_upwards [hnot] with s hs
  apply propext
  change (a ≤ inner ℝ (u : Space) (s : Space) ∧ inner ℝ (u : Space) (s : Space) ≤ b) ↔
    (a ≤ inner ℝ (u : Space) (s : Space) ∧ ¬ b ≤ inner ℝ (u : Space) (s : Space))
  rw [not_le]
  exact and_congr_right (fun _ => le_iff_lt_or_eq.trans (or_iff_left hs))
end QEC.Coding.ProbabilisticConstruction.SphericalCap

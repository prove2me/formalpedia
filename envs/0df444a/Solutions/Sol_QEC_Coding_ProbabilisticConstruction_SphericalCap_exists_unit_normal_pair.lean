-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.exists_unit_normal_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:39:37.7635+00:00
-- url     : https://prove2.me/submissions/43b1461b-4fd5-428d-9b85-6a21738af93b

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (b c : Space) :
    ∃ n : Space, ‖n‖ = 1 ∧ inner ℝ n b = 0 ∧ inner ℝ n c = 0 := by
  classical
  let K := Submodule.span ℝ ({b,c} : Set Space)
  have hdim : Module.finrank ℝ K ≤ 2 := by
    have h := finrank_span_le_card (R := ℝ) ({b,c} : Set Space)
    apply h.trans
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  have hadd := K.finrank_add_finrank_orthogonal
  have hpos : 0 < Module.finrank ℝ Kᗮ := by
    have he : Module.finrank ℝ Space = 3 := by simp [Space]
    rw [he] at hadd
    omega
  obtain ⟨v,hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hv0 : (v : Space) ≠ 0 := by simpa using hv
  have hn : ‖(v : Space)‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  refine ⟨‖(v : Space)‖⁻¹ • (v : Space), ?_, ?_, ?_⟩
  · simp [norm_smul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), hn]
  · rw [real_inner_smul_left]
    have hi : inner ℝ (v : Space) b = 0 :=
      (K.mem_orthogonal' _).mp v.property b (Submodule.subset_span (by simp))
    rw [hi,mul_zero]
  · rw [real_inner_smul_left]
    have hi : inner ℝ (v : Space) c = 0 :=
      (K.mem_orthogonal' _).mp v.property c (Submodule.subset_span (by simp))
    rw [hi,mul_zero]
end QEC.Coding.ProbabilisticConstruction.SphericalCap

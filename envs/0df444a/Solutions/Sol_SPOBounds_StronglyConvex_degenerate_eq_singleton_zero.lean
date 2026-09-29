-- Prove2me | solution 1 for SPOBounds.StronglyConvex.degenerate_eq_singleton_zero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:12:23.134852+00:00
-- url     : https://prove2.me/submissions/3baf5afd-c9ec-40be-ab23-6fb5788d5e24

import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy
import Definitions.Def_SPOBounds_StronglyConvex_StronglyConvexSet

namespace SPOBounds.StronglyConvex

theorem aux_degsz_exists_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : StrongDual ℝ E) (hc : c ≠ 0) : ∃ y, 0 < c y := by
  by_contra h
  push Not at h
  apply hc
  ext x
  have h1 := h x
  have h2 := h (-x)
  rw [map_neg] at h2
  simp only [zero_apply]
  linarith

end SPOBounds.StronglyConvex

open SPOBounds.StronglyConvex

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hSc : IsCompact S) (hSnt : S.Nontrivial)
    {μbar : ℝ} (hμ : 0 < μbar) (hSsc : StronglyConvexSet μbar S) :
    SPOBounds.Shared.degenerate S = {0} := by
  ext c
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, hu, v, hv, huv, hmu, hmv⟩
    by_contra hc
    have hcuv : c u = c v := le_antisymm (hmu hv) (hmv hu)
    obtain ⟨y, hy⟩ := aux_degsz_exists_pos c hc
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have huv' : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
    set r := (μbar / 2) * (1/2:ℝ) * (1 - 1/2) * ‖u - v‖ ^ 2 with hr
    have hrpos : 0 < r := by positivity
    have hx : (1/2:ℝ) • u + (1 - 1/2:ℝ) • v - (r / ‖y‖) • y ∈ S := by
      apply hSsc.2 u hu v hv (1/2) ⟨by norm_num, by norm_num⟩
      rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_pos (div_pos hrpos hynorm), div_mul_cancel₀ _ hynorm.ne']
    have h1 : c u ≤ c ((1/2:ℝ) • u + (1 - 1/2:ℝ) • v - (r / ‖y‖) • y) := hmu hx
    simp only [map_sub, map_add, map_smul, smul_eq_mul] at h1
    rw [← hcuv] at h1
    have : 0 < r / ‖y‖ * c y := mul_pos (div_pos hrpos hynorm) hy
    linarith
  · rintro rfl
    obtain ⟨u, hu, v, hv, huv⟩ := hSnt
    exact ⟨u, hu, v, hv, huv, fun x _ => by simp, fun x _ => by simp⟩

-- Prove2me | solution 1 for SPOBounds.StronglyConvex.nu_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:47:26.436657+00:00
-- url     : https://prove2.me/submissions/c1c57b3d-8ff7-406d-932b-b36ee3b68b71

import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy
import Definitions.Def_SPOBounds_StronglyConvex_StronglyConvexSet

namespace SPOBounds.StronglyConvex

theorem aux_nueqn_degenerate_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hSnt : S.Nontrivial)
    {μbar : ℝ} (hμ : 0 < μbar) (hSsc : StronglyConvexSet μbar S) :
    SPOBounds.Shared.degenerate S = {0} := by
  ext c
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, hu, v, hv, huv, hminu, hminv⟩
    by_contra hc
    obtain ⟨x, hx⟩ := (DFunLike.ne_iff).1 hc
    simp only [zero_apply] at hx
    set x' : E := (c x)⁻¹ • x with hx'
    have hcx' : c x' = 1 := by
      rw [hx', map_smul, smul_eq_mul, inv_mul_cancel₀ hx]
    have hx'ne : x' ≠ 0 := by
      intro h; rw [h, map_zero] at hcx'; exact zero_ne_one hcx'
    have hnx' : 0 < ‖x'‖ := norm_pos_iff.2 hx'ne
    set w : E := (1/2 : ℝ) • u + (1 - 1/2 : ℝ) • v with hw
    set r : ℝ := (μbar / 2) * (1/2) * (1 - 1/2) * ‖u - v‖ ^ 2 with hr
    have huv' : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 huv)
    have hrpos : 0 < r := by rw [hr]; positivity
    have hball := hSsc.2 u hu v hv (1/2) ⟨by norm_num, by norm_num⟩
    set y : E := w - (r / ‖x'‖) • x' with hy
    have hyS : y ∈ S := by
      apply hball
      rw [Metric.mem_closedBall, dist_eq_norm, hy, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_pos (div_pos hrpos hnx'), div_mul_cancel₀ _ hnx'.ne']
    have h1 : c u ≤ c v := hminu hv
    have h2 : c v ≤ c u := hminv hu
    have hcw : c w = c u := by
      rw [hw, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      have : c v = c u := le_antisymm h2 h1
      rw [this]; ring
    have hcy : c y < c u := by
      rw [hy, map_sub, map_smul, hcx', smul_eq_mul, mul_one, hcw]
      linarith [div_pos hrpos hnx']
    have h3 : c u ≤ c y := hminu hyS
    linarith
  · rintro rfl
    obtain ⟨u, hu, v, hv, huv⟩ := hSnt
    refine ⟨u, hu, v, hv, huv, ?_, ?_⟩
    · intro z _; simp
    · intro z _; simp

end SPOBounds.StronglyConvex

open SPOBounds.StronglyConvex

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hSc : IsCompact S) (hSnt : S.Nontrivial)
    {μbar : ℝ} (hμ : 0 < μbar) (hSsc : StronglyConvexSet μbar S) :
    ∀ chat : StrongDual ℝ E, SPOBounds.Shared.nu S chat = ‖chat‖ := by
  intro chat
  unfold SPOBounds.Shared.nu
  rw [aux_nueqn_degenerate_eq hSnt hμ hSsc, Metric.infDist_singleton, dist_zero_right]

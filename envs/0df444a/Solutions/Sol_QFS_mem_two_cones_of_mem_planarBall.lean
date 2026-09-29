-- Prove2me | solution 1 for QFS.mem_two_cones_of_mem_planarBall
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:03:07.98488+00:00
-- url     : https://prove2.me/submissions/0e20d1c0-3ec5-4d70-93ab-328cb26b0c23

import Theorems.Thm_QFS_closedBall_subset_cone
import Theorems.Thm_QFS_coneGap_smul_axis
import Theorems.Thm_QFS_mem_cone_iff_coneGap_pos
import Theorems.Thm_QFS_norm_sq_eq_inner_sq_add


import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Section1
import Definitions.Def_QFS_ThinCones
import Definitions.Def_QFS_Section3Kernel
import Definitions.Def_QFS_LebesgueDiff
import Definitions.Def_QFS_LebesgueDiff2
import Definitions.Def_QFS_Renormalization
import Definitions.Def_QFS_FirstJump
import Definitions.Def_QFS_Assembly
import Definitions.Def_QFS_PathAssembly
import Definitions.Def_QFS_BlockPaths
import Definitions.Def_QFS_Section6
import Definitions.Def_QFS_Rescaling
import Definitions.Def_QFS_Section32
import Definitions.Def_QFS_AppendixA
import Definitions.Def_QFS_BeyondThePaper
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Metric Set MeasureTheory
open scoped Real InnerProductSpace ENNReal

open QFS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]



namespace QFSProof_mem_two_cones_of_mem_planarBall

@[simp] lemma perp2_apply_zero (w : EuclideanSpace ℝ (Fin 2)) : perp2 w 0 = -(w 1) := rfl

@[simp] lemma perp2_apply_one (w : EuclideanSpace ℝ (Fin 2)) : perp2 w 1 = w 0 := rfl

lemma real_inner_eq_two (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

lemma norm_sq_eq_two (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, real_inner_eq_two]
  ring

lemma norm_perp2 (w : EuclideanSpace ℝ (Fin 2)) : ‖perp2 w‖ = ‖w‖ := by
  have h : ‖perp2 w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [norm_sq_eq_two, norm_sq_eq_two]; simp; ring
  have h1 : (0:ℝ) ≤ ‖perp2 w‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖w‖ := norm_nonneg _
  nlinarith [h, h1, h2]

lemma decomp_two {w : EuclideanSpace ℝ (Fin 2)} (hw : ‖w‖ = 1)
    (x : EuclideanSpace ℝ (Fin 2)) :
    x = ⟪w, x⟫_ℝ • w + ⟪perp2 w, x⟫_ℝ • perp2 w := by
  have hw2 : (w 0) ^ 2 + (w 1) ^ 2 = 1 := by
    rw [← norm_sq_eq_two, hw]; norm_num
  refine euclidean_ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · simp only [real_inner_eq_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      perp2_apply_zero, perp2_apply_one]
    linear_combination (-(x 0)) * hw2
  · simp only [real_inner_eq_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      perp2_apply_zero, perp2_apply_one]
    linear_combination (-(x 1)) * hw2

lemma norm_across_two {w : EuclideanSpace ℝ (Fin 2)} (hw : ‖w‖ = 1)
    (x : EuclideanSpace ℝ (Fin 2)) : ‖across w x‖ = |⟪perp2 w, x⟫_ℝ| := by
  have hd := decomp_two hw x
  have hacross : across w x = ⟪perp2 w, x⟫_ℝ • perp2 w := by
    rw [across]
    nth_rewrite 1 [hd]
    abel
  rw [hacross, norm_smul, Real.norm_eq_abs, norm_perp2, hw, mul_one]

lemma inner_perp2_eq_neg_cross (u x : EuclideanSpace ℝ (Fin 2)) :
    ⟪perp2 u, x⟫_ℝ = -cross2 x u := by
  rw [real_inner_eq_two, cross2]
  simp
  ring

lemma norm_across_eq_abs_cross {u : EuclideanSpace ℝ (Fin 2)} (hu : ‖u‖ = 1)
    (x : EuclideanSpace ℝ (Fin 2)) : ‖across u x‖ = |cross2 x u| := by
  rw [norm_across_two hu, inner_perp2_eq_neg_cross, abs_neg]

lemma cramer2 (x a b : EuclideanSpace ℝ (Fin 2)) :
    cross2 x b • a - cross2 x a • b = cross2 a b • x := by
  refine euclidean_ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
    · simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, cross2]
      ring

lemma abs_cross_ge_of_notMem_doubleCone {u : EuclideanSpace ℝ (Fin 2)} (hu : ‖u‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∉ doubleCone u ϑ) : ‖x‖ * Real.sin ϑ ≤ |cross2 x u| := by
  have hs : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos ϑ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hϑ'⟩
  have hsc : Real.sin ϑ ^ 2 + Real.cos ϑ ^ 2 = 1 := Real.sin_sq_add_cos_sq ϑ
  rw [mem_doubleCone_iff] at hx
  simp only [not_or] at hx
  obtain ⟨h1, h2⟩ := hx
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [cross2]
  have hg1 : coneGap u ϑ x ≤ 0 := by
    by_contra hcon
    exact h1 ((QFS.mem_cone_iff_coneGap_pos hu hϑ hϑ' x).mpr (not_le.mp hcon))
  have hg2 : coneGap u ϑ (-x) ≤ 0 := by
    by_contra hcon
    exact h2 ((QFS.mem_cone_iff_coneGap_pos hu hϑ hϑ' (-x)).mpr (not_le.mp hcon))
  have hacross : across u (-x) = -across u x := by
    simp [across, inner_neg_right, neg_smul]
    abel
  rw [coneGap, hacross, norm_neg, inner_neg_right] at hg2
  rw [coneGap] at hg1

  have hpy := QFS.norm_sq_eq_inner_sq_add hu x
  have hB : ‖across u x‖ = |cross2 x u| := norm_across_eq_abs_cross hu x
  have hBnn : 0 ≤ ‖across u x‖ := norm_nonneg _
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  rw [← hB]
  nlinarith [hg1, hg2, hpy, hBnn, hxn, hs, hc, hsc, sq_nonneg (⟪u, x⟫_ℝ)]

lemma cone_neg_subset_doubleCone (v : E) (ϑ : ℝ) : cone (-v) ϑ ⊆ doubleCone v ϑ := by
  intro h hh
  rw [mem_doubleCone_iff]
  refine Or.inr ⟨neg_ne_zero.mpr hh.1, ?_⟩
  have h2 := hh.2
  rw [inner_neg_left] at h2
  rwa [inner_neg_right, norm_neg]

lemma abs_cross_le (u w : EuclideanSpace ℝ (Fin 2)) : |cross2 u w| ≤ ‖u‖ * ‖w‖ := by
  have hinner : ⟪perp2 u, w⟫_ℝ = cross2 u w := by
    rw [inner_perp2_eq_neg_cross, cross2, cross2]; ring
  have := abs_real_inner_le_norm (perp2 u) w
  rw [hinner, norm_perp2] at this
  exact this

end QFSProof_mem_two_cones_of_mem_planarBall
open QFSProof_mem_two_cones_of_mem_planarBall

set_option autoImplicit false

theorem solution {vs vt : EuclideanSpace ℝ (Fin 2)}
    (hvs : ‖vs‖ = 1) (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {s t : EuclideanSpace ℝ (Fin 2)} (hst : s ≠ t) (hD : cross2 vs vt ≠ 0)
    (hns : t - s ∉ doubleCone vs ϑ) (hnt : t - s ∉ doubleCone vt ϑ)
    {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2)) :
    y - s ∈ doubleCone vs ϑ ∧ y - t ∈ doubleCone vt ϑ := by
  have hs : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hδ : 0 < ‖t - s‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero_of_ne (Ne.symm hst)
  have hDpos : 0 < |cross2 vs vt| := abs_pos.mpr hD
  have hD1 : |cross2 vs vt| ≤ 1 := by
    have := abs_cross_le vs vt
    rwa [hvs, hvt, mul_one] at this
  set ρ : ℝ := ‖t - s‖ * Real.sin ϑ ^ 2 / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; positivity

  have key : ∀ (u : EuclideanSpace ℝ (Fin 2)), ‖u‖ = 1 → ∀ c : ℝ,
      ‖t - s‖ * Real.sin ϑ ≤ |c| → ∀ y : EuclideanSpace ℝ (Fin 2),
      ‖y - c • u‖ ≤ ρ → y ∈ doubleCone u ϑ := by
    intro u hu c hc y hy
    have hgap : ρ < |c| * Real.sin ϑ := by
      have h1 : ‖t - s‖ * Real.sin ϑ * Real.sin ϑ ≤ |c| * Real.sin ϑ :=
        mul_le_mul_of_nonneg_right hc hs.le
      rw [hρdef]
      nlinarith [h1, hδ, hs]
    rcases lt_or_gt_of_ne (show c ≠ 0 by
      intro hc0
      rw [hc0, abs_zero] at hc
      nlinarith [hδ, hs]) with hneg | hpos
    · refine cone_neg_subset_doubleCone u ϑ ?_
      have hun : ‖-u‖ = 1 := by rw [norm_neg, hu]
      have hcc : c • u = (-c) • (-u) := by rw [smul_neg, neg_smul, neg_neg]
      refine QFS.closedBall_subset_cone hun hϑ hϑ' (p := (-c) • (-u)) (ρ := ρ) ?_ ?_
      · rw [QFS.coneGap_smul_axis hun ϑ (-c)]
        rw [abs_of_neg hneg] at hgap
        exact hgap
      · rw [Metric.mem_closedBall, dist_eq_norm, ← hcc]
        exact hy
    · refine Set.mem_union_left _ ?_
      refine QFS.closedBall_subset_cone hu hϑ hϑ' (p := c • u) (ρ := ρ) ?_ ?_
      · rw [QFS.coneGap_smul_axis hu ϑ c]
        rw [abs_of_pos hpos] at hgap
        exact hgap
      · rw [Metric.mem_closedBall, dist_eq_norm]
        exact hy

  set a : ℝ := cross2 (t - s) vt / cross2 vs vt with hadef
  set b : ℝ := cross2 (t - s) vs / cross2 vs vt with hbdef
  have hzs : (s + a • vs) - s = a • vs := by abel
  have hzt : (s + a • vs) - t = b • vt := by
    have hcr := cramer2 (t - s) vs vt
    have hsm : a • vs - b • vt = t - s := by
      have h1 : a • vs = (cross2 vs vt)⁻¹ • (cross2 (t - s) vt • vs) := by
        rw [hadef, smul_smul, div_eq_inv_mul]
      have h2 : b • vt = (cross2 vs vt)⁻¹ • (cross2 (t - s) vs • vt) := by
        rw [hbdef, smul_smul, div_eq_inv_mul]
      rw [h1, h2, ← smul_sub, hcr, smul_smul, inv_mul_cancel₀ hD, one_smul]
    have : (s + a • vs) - t = (a • vs - b • vt) - (t - s) + b • vt := by abel
    rw [this, hsm, sub_self, zero_add]

  have hlowa : ‖t - s‖ * Real.sin ϑ ≤ |a| := by
    have h1 := abs_cross_ge_of_notMem_doubleCone hvt hϑ hϑ' hnt
    rw [hadef, abs_div]
    rw [le_div_iff₀ hDpos]
    nlinarith [h1, hD1, hδ, hs, abs_nonneg (cross2 (t - s) vt)]
  have hlowb : ‖t - s‖ * Real.sin ϑ ≤ |b| := by
    have h1 := abs_cross_ge_of_notMem_doubleCone hvs hϑ hϑ' hns
    rw [hbdef, abs_div]
    rw [le_div_iff₀ hDpos]
    nlinarith [h1, hD1, hδ, hs, abs_nonneg (cross2 (t - s) vs)]
  have hctr : planarCtr vs vt s t = s + a • vs := by
    rw [planarCtr, planarA, ← hadef]
  rw [Metric.mem_closedBall, dist_eq_norm, hctr] at hy
  constructor
  · refine key vs hvs a hlowa (y - s) ?_
    have h : (y - s) - a • vs = y - (s + a • vs) := by abel
    rw [h]; exact hy
  · refine key vt hvt b hlowb (y - t) ?_
    have h : (y - t) - b • vt = y - (s + a • vs) := by rw [← hzt]; abel
    rw [h]; exact hy
#print axioms solution

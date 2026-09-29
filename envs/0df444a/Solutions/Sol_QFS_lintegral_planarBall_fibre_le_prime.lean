-- Prove2me | solution 1 for QFS.lintegral_planarBall_fibre_le_prime
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:03:07.059716+00:00
-- url     : https://prove2.me/submissions/2682181e-e0f7-41db-a874-87b546a90c7f

import Theorems.Thm_QFS_measurableSet_planarBall_fibre_prime
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



namespace QFSProof_lintegral_planarBall_fibre_le_prime

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

lemma abs_cross_le (u w : EuclideanSpace ℝ (Fin 2)) : |cross2 u w| ≤ ‖u‖ * ‖w‖ := by
  have hinner : ⟪perp2 u, w⟫_ℝ = cross2 u w := by
    rw [inner_perp2_eq_neg_cross, cross2, cross2]; ring
  have := abs_real_inner_le_norm (perp2 u) w
  rw [hinner, norm_perp2] at this
  exact this

lemma planarCtr_sub_left (vs vt s t : EuclideanSpace ℝ (Fin 2)) :
    planarCtr vs vt s t - s = planarA vs vt s t • vs := by
  rw [planarCtr]; abel

lemma planarCtr_sub_right {vs vt : EuclideanSpace ℝ (Fin 2)} (hD : cross2 vs vt ≠ 0)
    (s t : EuclideanSpace ℝ (Fin 2)) :
    planarCtr vs vt s t - t = planarB vs vt s t • vt := by
  have hcr := cramer2 (t - s) vs vt
  have hsm : planarA vs vt s t • vs - planarB vs vt s t • vt = t - s := by
    have h1 : planarA vs vt s t • vs
        = (cross2 vs vt)⁻¹ • (cross2 (t - s) vt • vs) := by
      rw [planarA, smul_smul, div_eq_inv_mul]
    have h2 : planarB vs vt s t • vt
        = (cross2 vs vt)⁻¹ • (cross2 (t - s) vs • vt) := by
      rw [planarB, smul_smul, div_eq_inv_mul]
    rw [h1, h2, ← smul_sub, hcr, smul_smul, inv_mul_cancel₀ hD, one_smul]
  have hrw : planarCtr vs vt s t - t
      = (planarA vs vt s t • vs - planarB vs vt s t • vt) - (t - s)
        + planarB vs vt s t • vt := by
    rw [planarCtr]; abel
  rw [hrw, hsm, sub_self, zero_add]

lemma norm_planarCtr_sub_left (vs vt s t : EuclideanSpace ℝ (Fin 2)) (hvs : ‖vs‖ = 1) :
    ‖planarCtr vs vt s t - s‖ = |planarA vs vt s t| := by
  rw [planarCtr_sub_left, norm_smul, Real.norm_eq_abs, hvs, mul_one]

lemma norm_planarCtr_sub_right {vs vt : EuclideanSpace ℝ (Fin 2)} (hD : cross2 vs vt ≠ 0)
    (s t : EuclideanSpace ℝ (Fin 2)) (hvt : ‖vt‖ = 1) :
    ‖planarCtr vs vt s t - t‖ = |planarB vs vt s t| := by
  rw [planarCtr_sub_right hD, norm_smul, Real.norm_eq_abs, hvt, mul_one]

lemma planarA_bounds {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1) (hvt : ‖vt‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {s t : EuclideanSpace ℝ (Fin 2)}
    (hD : cross2 vs vt ≠ 0) (hnt : t - s ∉ doubleCone vt ϑ) :
    ‖t - s‖ * Real.sin ϑ ≤ |planarA vs vt s t| ∧
      |planarA vs vt s t| ≤ ‖t - s‖ / |cross2 vs vt| := by
  have hDpos : 0 < |cross2 vs vt| := abs_pos.mpr hD
  have hD1 : |cross2 vs vt| ≤ 1 := by
    have h := abs_cross_le vs vt
    rwa [hvs, hvt, mul_one] at h
  have hlow := abs_cross_ge_of_notMem_doubleCone hvt hϑ hϑ' hnt
  have hup : |cross2 (t - s) vt| ≤ ‖t - s‖ := by
    have h := abs_cross_le (t - s) vt
    rwa [hvt, mul_one] at h
  have habs : |planarA vs vt s t| = |cross2 (t - s) vt| / |cross2 vs vt| := by
    rw [planarA, abs_div]
  have hsinnn : 0 ≤ Real.sin ϑ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hϑ.le (by linarith [Real.pi_pos])
  constructor
  · rw [habs, le_div_iff₀ hDpos]
    calc ‖t - s‖ * Real.sin ϑ * |cross2 vs vt|
        ≤ ‖t - s‖ * Real.sin ϑ * 1 :=
          mul_le_mul_of_nonneg_left hD1 (by positivity)
      _ = ‖t - s‖ * Real.sin ϑ := mul_one _
      _ ≤ |cross2 (t - s) vt| := hlow
  · rw [habs]
    gcongr

lemma planarB_bounds {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1) (hvt : ‖vt‖ = 1)
    {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {s t : EuclideanSpace ℝ (Fin 2)}
    (hD : cross2 vs vt ≠ 0) (hns : t - s ∉ doubleCone vs ϑ) :
    ‖t - s‖ * Real.sin ϑ ≤ |planarB vs vt s t| ∧
      |planarB vs vt s t| ≤ ‖t - s‖ / |cross2 vs vt| := by
  have hDpos : 0 < |cross2 vs vt| := abs_pos.mpr hD
  have hD1 : |cross2 vs vt| ≤ 1 := by
    have h := abs_cross_le vs vt
    rwa [hvs, hvt, mul_one] at h
  have hlow := abs_cross_ge_of_notMem_doubleCone hvs hϑ hϑ' hns
  have hup : |cross2 (t - s) vs| ≤ ‖t - s‖ := by
    have h := abs_cross_le (t - s) vs
    rwa [hvs, mul_one] at h
  have habs : |planarB vs vt s t| = |cross2 (t - s) vs| / |cross2 vs vt| := by
    rw [planarB, abs_div]
  have hsinnn : 0 ≤ Real.sin ϑ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hϑ.le (by linarith [Real.pi_pos])
  constructor
  · rw [habs, le_div_iff₀ hDpos]
    calc ‖t - s‖ * Real.sin ϑ * |cross2 vs vt|
        ≤ ‖t - s‖ * Real.sin ϑ * 1 :=
          mul_le_mul_of_nonneg_left hD1 (by positivity)
      _ = ‖t - s‖ * Real.sin ϑ := mul_one _
      _ ≤ |cross2 (t - s) vs| := hlow
  · rw [habs]
    gcongr

theorem planarBall_comparable {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1)
    (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2)
    {s t : EuclideanSpace ℝ (Fin 2)} (hD : cross2 vs vt ≠ 0)
    (hns : t - s ∉ doubleCone vs ϑ) (hnt : t - s ∉ doubleCone vt ϑ)
    {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2)) :
    ‖t - s‖ * Real.sin ϑ / 2 ≤ ‖z - s‖ ∧
      ‖z - s‖ ≤ ‖t - s‖ * (1 / |cross2 vs vt| + 1) ∧
      ‖t - s‖ * Real.sin ϑ / 2 ≤ ‖z - t‖ ∧
      ‖z - t‖ ≤ ‖t - s‖ * (1 / |cross2 vs vt| + 1) := by
  have hDpos : 0 < |cross2 vs vt| := abs_pos.mpr hD
  have hs0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hs1 : Real.sin ϑ ≤ 1 := Real.sin_le_one ϑ
  have hδ : 0 ≤ ‖t - s‖ := norm_nonneg _
  obtain ⟨hAlow, hAup⟩ := planarA_bounds hvs hvt hϑ hϑ' hD hnt
  obtain ⟨hBlow, hBup⟩ := planarB_bounds hvs hvt hϑ hϑ' hD hns
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hAeq := norm_planarCtr_sub_left vs vt s t hvs
  have hBeq := norm_planarCtr_sub_right hD s t hvt
  have hsplit : ∀ c : EuclideanSpace ℝ (Fin 2),
      ‖planarCtr vs vt s t - c‖ - ‖t - s‖ * Real.sin ϑ ^ 2 / 2 ≤ ‖z - c‖ ∧
      ‖z - c‖ ≤ ‖planarCtr vs vt s t - c‖ + ‖t - s‖ * Real.sin ϑ ^ 2 / 2 := by
    intro c
    have h1 : ‖z - c‖ ≤ ‖z - planarCtr vs vt s t‖ + ‖planarCtr vs vt s t - c‖ := by
      have : z - c = (z - planarCtr vs vt s t) + (planarCtr vs vt s t - c) := by abel
      rw [this]; exact norm_add_le _ _
    have h2 : ‖planarCtr vs vt s t - c‖ ≤ ‖planarCtr vs vt s t - z‖ + ‖z - c‖ := by
      have : planarCtr vs vt s t - c = (planarCtr vs vt s t - z) + (z - c) := by abel
      rw [this]; exact norm_add_le _ _
    rw [norm_sub_rev (planarCtr vs vt s t) z] at h2
    constructor <;> linarith
  obtain ⟨hL1, hU1⟩ := hsplit s
  obtain ⟨hL2, hU2⟩ := hsplit t
  rw [hAeq] at hL1 hU1
  rw [hBeq] at hL2 hU2
  have hdiv : ‖t - s‖ / |cross2 vs vt| = ‖t - s‖ * (1 / |cross2 vs vt|) := by ring
  have hsq : Real.sin ϑ ^ 2 ≤ 1 := by nlinarith [hs0, hs1]
  have hprod : ‖t - s‖ * Real.sin ϑ ^ 2 ≤ ‖t - s‖ * 1 := mul_le_mul_of_nonneg_left hsq hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [hAlow, hL1, hδ, hs0, hs1]
  · rw [hdiv] at hAup; nlinarith [hAup, hU1, hδ, hprod]
  · nlinarith [hBlow, hL2, hδ, hs0, hs1]
  · rw [hdiv] at hBup; nlinarith [hBup, hU2, hδ, hprod]

theorem planarBall_comparable'' {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1)
    (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) (hD : cross2 vs vt ≠ 0)
    {s t z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ planarBall vs vt ϑ s t) :
    ‖t - s‖ * Real.sin ϑ / 2 ≤ ‖z - t‖ ∧
      ‖z - t‖ ≤ ‖t - s‖ * (1 / |cross2 vs vt| + 1) :=
  let h := planarBall_comparable hvs hvt hϑ hϑ' hD hz.2.1 hz.2.2.1 hz.2.2.2
  ⟨h.2.2.1, h.2.2.2⟩

end QFSProof_lintegral_planarBall_fibre_le_prime
open QFSProof_lintegral_planarBall_fibre_le_prime

set_option autoImplicit false

theorem solution {vs vt : EuclideanSpace ℝ (Fin 2)} (hvs : ‖vs‖ = 1)
    (hvt : ‖vt‖ = 1) {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) {α : ℝ} (hα : 0 ≤ α)
    (hD : cross2 vs vt ≠ 0) (t z : EuclideanSpace ℝ (Fin 2)) :
    ∫⁻ s in {s | z ∈ planarBall vs vt ϑ s t},
        ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α))
      ≤ ENNReal.ofReal (planarConst vs vt ϑ α * ‖z - t‖ ^ (-(2 : ℝ) - α)) * unitBallVol 2 := by
  have hs0 : 0 < Real.sin ϑ := Real.sin_pos_of_pos_of_lt_pi hϑ (by linarith [Real.pi_pos])
  have hDpos : 0 < |cross2 vs vt| := abs_pos.mpr hD
  have hA : (0 : ℝ) < 1 / |cross2 vs vt| + 1 := by positivity
  have hmeas := QFS.measurableSet_planarBall_fibre_prime (vs := vs) (vt := vt) ϑ t z
  have hsub : {s | z ∈ planarBall vs vt ϑ s t} ⊆ closedBall t (2 * ‖z - t‖ / Real.sin ϑ) := by
    intro s hs
    obtain ⟨hlow, -⟩ := planarBall_comparable'' hvs hvt hϑ hϑ' hD hs
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev s t, le_div_iff₀ hs0]
    linarith
  rcases eq_or_ne z t with rfl | hzt
  · have hball0 : volume (closedBall z (0 : ℝ)) = 0 := by
      rw [volume_closedBall_eq _ le_rfl]; norm_num
    have hnull : volume {s : EuclideanSpace ℝ (Fin 2) | z ∈ planarBall vs vt ϑ s z} = 0 := by
      refine measure_mono_null (le_trans hsub (le_of_eq ?_)) hball0
      simp
    rw [setLIntegral_measure_zero _ _ hnull]
    simp
  · have hn : 0 < ‖z - t‖ := by rw [norm_pos_iff]; exact sub_ne_zero_of_ne hzt
    have hexp : -(4 : ℝ) - α ≤ 0 := by linarith
    have hquot : 0 < ‖z - t‖ / (1 / |cross2 vs vt| + 1) := by positivity
    have hpt : ∀ s ∈ {s | z ∈ planarBall vs vt ϑ s t},
        ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α))
          ≤ ENNReal.ofReal ((‖z - t‖ / (1 / |cross2 vs vt| + 1)) ^ (-(4 : ℝ) - α)) := by
      intro s hs
      obtain ⟨-, hup⟩ := planarBall_comparable'' hvs hvt hϑ hϑ' hD hs
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hquot ?_ hexp)
      rw [div_le_iff₀ hA, norm_sub_rev s t]
      linarith
    calc ∫⁻ s in {s | z ∈ planarBall vs vt ϑ s t},
            ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α))
        ≤ ∫⁻ _ in {s | z ∈ planarBall vs vt ϑ s t},
            ENNReal.ofReal ((‖z - t‖ / (1 / |cross2 vs vt| + 1)) ^ (-(4 : ℝ) - α)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hmeas] with s hs using hpt s hs
      _ = ENNReal.ofReal ((‖z - t‖ / (1 / |cross2 vs vt| + 1)) ^ (-(4 : ℝ) - α)) *
            volume {s | z ∈ planarBall vs vt ϑ s t} := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal ((‖z - t‖ / (1 / |cross2 vs vt| + 1)) ^ (-(4 : ℝ) - α)) *
            volume (closedBall t (2 * ‖z - t‖ / Real.sin ϑ)) :=
          mul_le_mul' le_rfl (measure_mono hsub)
      _ = ENNReal.ofReal (planarConst vs vt ϑ α * ‖z - t‖ ^ (-(2 : ℝ) - α)) *
            unitBallVol 2 := by
          rw [volume_closedBall_eq _ (by positivity), ← mul_assoc,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hquot.le _)]
          congr 2
          have e1 : (‖z - t‖ / (1 / |cross2 vs vt| + 1)) ^ (-(4 : ℝ) - α)
              = ‖z - t‖ ^ (-(4 : ℝ) - α) * (1 / |cross2 vs vt| + 1) ^ (4 + α) := by
            rw [Real.div_rpow hn.le hA.le,
              show -(4 : ℝ) - α = -(4 + α) from by ring, Real.rpow_neg hA.le,
              div_eq_mul_inv, inv_inv]
          have e2 : (2 * ‖z - t‖ / Real.sin ϑ) ^ 2
              = ‖z - t‖ ^ ((2 : ℕ) : ℝ) * (4 / Real.sin ϑ ^ 2) := by
            rw [Real.rpow_natCast]
            field_simp
            ring
          have e3 : ‖z - t‖ ^ (-(4 : ℝ) - α) * ‖z - t‖ ^ ((2 : ℕ) : ℝ)
              = ‖z - t‖ ^ (-(2 : ℝ) - α) := by
            rw [← Real.rpow_add hn]; congr 1; push_cast; ring
          rw [e1, e2, planarConst]
          rw [show ‖z - t‖ ^ (-(4 : ℝ) - α) * (1 / |cross2 vs vt| + 1) ^ (4 + α) *
                (‖z - t‖ ^ ((2 : ℕ) : ℝ) * (4 / Real.sin ϑ ^ 2))
              = (‖z - t‖ ^ (-(4 : ℝ) - α) * ‖z - t‖ ^ ((2 : ℕ) : ℝ)) *
                ((1 / |cross2 vs vt| + 1) ^ (4 + α) * 4 / Real.sin ϑ ^ 2) from by ring, e3]
          ring
#print axioms solution

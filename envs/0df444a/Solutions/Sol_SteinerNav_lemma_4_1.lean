-- Prove2me | solution 1 for SteinerNav.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:24:07.385832+00:00
-- url     : https://prove2.me/submissions/ecf35c88-078a-4b77-8171-eb929d39c855

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing
import Definitions.Def_SteinerNav_annularCandidates

open SteinerNav MeasureTheory RegretBandits.Nonlinear
open scoped Pointwise

namespace AuxLemma41

def capSet {d : ℕ} (a : ℝ) (v : Pt d) : Set (Pt d) :=
  {u : Pt d | ‖u‖ = 1 ∧ a < inner ℝ u v}

lemma measurableSet_capSet {d : ℕ} (a : ℝ) (v : Pt d) :
    MeasurableSet (capSet a v) := by
  have heq : capSet a v = Metric.sphere (0 : Pt d) 1 ∩ {u : Pt d | a < inner ℝ u v} := by
    ext u
    simp [capSet]
  rw [heq]
  have hcont : Continuous (fun u : Pt d => inner ℝ u v) :=
    continuous_id.inner continuous_const
  exact Metric.isClosed_sphere.measurableSet.inter (isOpen_lt continuous_const hcont).measurableSet

lemma samplingEps_formula {d : ℕ} (hd : 1 ≤ d) :
    samplingEps (1 + 1 / (d : ℝ)) = (2 * (d : ℝ) + 1) / ((d : ℝ) + 1) ^ 2 ∧
      0 < samplingEps (1 + 1 / (d : ℝ)) ∧ samplingEps (1 + 1 / (d : ℝ)) < 1 := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have hd1_pos : (0 : ℝ) < (d : ℝ) + 1 := by linarith
  have hα_eq : 1 + 1 / (d : ℝ) = ((d : ℝ) + 1) / (d : ℝ) := by
    field_simp
  have hform : samplingEps (1 + 1 / (d : ℝ)) = (2 * (d : ℝ) + 1) / ((d : ℝ) + 1) ^ 2 := by
    unfold samplingEps
    rw [hα_eq]
    field_simp
    ring
  refine ⟨hform, ?_, ?_⟩
  · rw [hform]
    positivity
  · rw [hform, div_lt_one (by positivity)]
    nlinarith

lemma cap_subset_covers {d : ℕ} (hd : 1 ≤ d) (s t : Pt d) (r₀ : ℝ)
    (hst : s ≠ t) (hr₀ : 0 < r₀) (hlo : r₀ ≤ dist s t) (hhi : dist s t ≤ 2 * r₀) :
    let α : ℝ := 1 + 1 / (d : ℝ)
    let ε : ℝ := samplingEps α
    let a : ℝ := 3 * Real.sqrt ε / (2 * Real.sqrt 2)
    let x : Pt d := (dist s t)⁻¹ • (t - s)
    ‖x‖ = 1 ∧
      capSet a x ⊆ {u : Pt d | Covers α s (s + (r₀ * Real.sqrt (2 * ε)) • u) t} := by
  dsimp only
  set α : ℝ := 1 + 1 / (d : ℝ)
  set ε : ℝ := samplingEps α
  obtain ⟨_, hε_pos, _⟩ := samplingEps_formula hd
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hα_pos : 0 < α := by positivity
  set r : ℝ := dist s t
  have hr_pos : 0 < r := dist_pos.mpr hst
  have hts_norm : ‖t - s‖ = r := by rw [← dist_eq_norm, dist_comm]
  set x : Pt d := r⁻¹ • (t - s)
  have hx_norm : ‖x‖ = 1 := by
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr_pos), hts_norm,
      inv_mul_cancel₀ (ne_of_gt hr_pos)]
  refine ⟨hx_norm, ?_⟩
  intro u hu
  obtain ⟨hu_norm, hu_inner⟩ := hu
  unfold Covers
  set β : ℝ := r₀ * Real.sqrt (2 * ε)
  have hβ_pos : 0 < β := by positivity
  have hdiff : (s + β • u) - t = β • u - r • x := by
    have hr_x : r • x = t - s := by
      dsimp [x]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr_pos), one_smul]
    rw [hr_x]
    abel
  have hdist_sq : dist (s + β • u) t ^ 2 =
      2 * r₀ ^ 2 * ε + r ^ 2 - 2 * r * r₀ * Real.sqrt (2 * ε) * inner ℝ u x := by
    rw [dist_eq_norm, hdiff, norm_sub_sq_real]
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hβ_pos, abs_of_pos hr_pos, hu_norm, hx_norm]
    rw [inner_smul_left, inner_smul_right]
    have hβ_sq : β ^ 2 = 2 * r₀ ^ 2 * ε := by
      dsimp [β]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    simp only [conj_trivial]
    nlinarith [hβ_sq]
  have hquad : 2 * r₀ ^ 2 + r ^ 2 ≤ 3 * r * r₀ := by
    have hprod : 0 ≤ (r - r₀) * (2 * r₀ - r) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hquad_ε : 2 * r₀ ^ 2 * ε + r ^ 2 * ε ≤ 3 * r * r₀ * ε := by
    have h1 := mul_le_mul_of_nonneg_right hquad (le_of_lt hε_pos)
    linarith
  have hinner_scaled : 3 * r * r₀ * ε < 2 * r * r₀ * Real.sqrt (2 * ε) * inner ℝ u x := by
    have hcoeff_pos : 0 < 2 * r * r₀ * Real.sqrt (2 * ε) := by positivity
    have hmul := mul_lt_mul_of_pos_left hu_inner hcoeff_pos
    have hlhs : 2 * r * r₀ * Real.sqrt (2 * ε) * (3 * Real.sqrt ε / (2 * Real.sqrt 2)) =
        3 * r * r₀ * ε := by
      have hsq2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
      rw [Real.sq_sqrt (le_of_lt hε_pos)]
    linarith
  have h1mε : 1 - ε = 1 / α ^ 2 := by
    have hdef : ε = 1 - 1 / α ^ 2 := rfl
    linarith
  have hsq_lt : dist (s + β • u) t ^ 2 < (r / α) ^ 2 := by
    have hrα : (r / α) ^ 2 = r ^ 2 * (1 - ε) := by
      rw [h1mε]
      field_simp
    linarith
  have hrα_pos : 0 < r / α := div_pos hr_pos hα_pos
  exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt hrα_pos) hsq_lt

lemma householder_exists {d : ℕ} (x y : Pt d) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ H : Pt d ≃ₗᵢ[ℝ] Pt d, H x = y ∧ ∀ v, H (H v) = v := by
  by_cases hxy : x = y
  · subst hxy
    exact ⟨LinearIsometryEquiv.refl ℝ (Pt d), rfl, fun _ => rfl⟩
  · let w : Pt d := x - y
    have hw_ne : w ≠ 0 := sub_ne_zero.mpr hxy
    have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
    have hw_sq_pos : 0 < ‖w‖ ^ 2 := sq_pos_of_pos hw_pos
    have hw_sq_ne : ‖w‖ ^ 2 ≠ 0 := ne_of_gt hw_sq_pos
    have hww : inner ℝ w w = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
    let f : Pt d →ₗ[ℝ] Pt d :=
      { toFun := fun v => v - (2 / ‖w‖ ^ 2 * inner ℝ w v) • w
        map_add' := fun u v => by
          rw [inner_add_right]
          ext i
          simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
          ring
        map_smul' := fun c v => by
          rw [inner_smul_right]
          ext i
          simp only [RingHom.id_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          ring }
    have hf_apply : ∀ v : Pt d, f v = v - (2 / ‖w‖ ^ 2 * inner ℝ w v) • w := fun _ => rfl
    have hf_invol : Function.Involutive f := by
      intro v
      rw [hf_apply (f v), hf_apply v]
      have hinner_fv : inner ℝ w (v - (2 / ‖w‖ ^ 2 * inner ℝ w v) • w) = - inner ℝ w v := by
        rw [inner_sub_right, inner_smul_right, hww]
        field_simp
        ring
      rw [hinner_fv]
      ext i
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    have hf_norm : ∀ v : Pt d, ‖f v‖ = ‖v‖ := by
      intro v
      rw [hf_apply]
      have hsq : ‖v - (2 / ‖w‖ ^ 2 * inner ℝ w v) • w‖ ^ 2 = ‖v‖ ^ 2 := by
        rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        rw [real_inner_comm v w]
        field_simp
        ring
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    have hf_x : f x = y := by
      rw [hf_apply]
      have hw_norm_sq : ‖w‖ ^ 2 = 2 - 2 * inner ℝ x y := by
        dsimp [w]
        rw [norm_sub_sq_real, hx, hy]
        ring
      have hwx : inner ℝ w x = ‖w‖ ^ 2 / 2 := by
        have h1 : inner ℝ w x = 1 - inner ℝ x y := by
          dsimp [w]
          rw [inner_sub_left, real_inner_self_eq_norm_sq, hx, real_inner_comm y x]
          ring
        linarith
      have hcoeff : 2 / ‖w‖ ^ 2 * inner ℝ w x = 1 := by
        rw [hwx]
        field_simp
      rw [hcoeff, one_smul]
      dsimp [w]
      abel
    let H : Pt d ≃ₗᵢ[ℝ] Pt d :=
      { toLinearEquiv := LinearEquiv.ofInvolutive f hf_invol
        norm_map' := hf_norm }
    exact ⟨H, hf_x, hf_invol⟩

lemma cone_cap_volume_eq {d : ℕ} (a : ℝ) (x y : Pt d) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    volume (Set.Ioo (0 : ℝ) 1 • capSet a x) = volume (Set.Ioo (0 : ℝ) 1 • capSet a y) := by
  obtain ⟨H, hHx, hInvol⟩ := householder_exists x y hx hy
  have hHy : H y = x := by rw [← hHx, hInvol]
  let e : Pt d ≃ᵐ Pt d := H.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving e volume volume := LinearIsometryEquiv.measurePreserving H
  have hpre : e ⁻¹' (Set.Ioo (0 : ℝ) 1 • capSet a y) = Set.Ioo (0 : ℝ) 1 • capSet a x := by
    ext z
    simp only [Set.mem_preimage, Set.mem_smul]
    constructor
    · rintro ⟨t, ht, u, ⟨hu_norm, hu_in⟩, hHz⟩
      refine ⟨t, ht, H u, ⟨?_, ?_⟩, ?_⟩
      · exact H.norm_map u ▸ hu_norm
      · have hin : inner ℝ (H u) x = inner ℝ u y := by
          rw [← hHy, H.inner_map_map]
        linarith
      · have h1 : H (e z) = H (t • u) := congrArg H hHz.symm
        have hez : H (e z) = z := hInvol z
        rw [hez, map_smul] at h1
        exact h1.symm
    · rintro ⟨t, ht, u, ⟨hu_norm, hu_in⟩, rfl⟩
      refine ⟨t, ht, H u, ⟨?_, ?_⟩, ?_⟩
      · exact H.norm_map u ▸ hu_norm
      · have hin : inner ℝ (H u) y = inner ℝ u x := by
          rw [← hHx, H.inner_map_map]
        linarith
      · change t • H u = H (t • u)
        exact (map_smul H t u).symm
  calc volume (Set.Ioo (0 : ℝ) 1 • capSet a x)
      = volume (e ⁻¹' (Set.Ioo (0 : ℝ) 1 • capSet a y)) := by rw [hpre]
    _ = (volume.map e) (Set.Ioo (0 : ℝ) 1 • capSet a y) :=
        (MeasurableEquiv.map_apply e _).symm
    _ = volume (Set.Ioo (0 : ℝ) 1 • capSet a y) := by rw [hmp.map_eq]

lemma sphereMeasure_cap_eq {d : ℕ} (a : ℝ) (v : Pt d) :
    sphereMeasure d (capSet a v) = (d : ENNReal) * volume (Set.Ioo (0 : ℝ) 1 • capSet a v) := by
  unfold sphereMeasure
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_capSet a v)]
  have hmeas_pre : MeasurableSet ((Subtype.val : Metric.sphere (0 : Pt d) 1 → Pt d) ⁻¹' capSet a v) :=
    (measurableSet_capSet a v).preimage measurable_subtype_coe
  rw [Measure.toSphere_apply' volume hmeas_pre, finrank_euclideanSpace_fin]
  have himg : Subtype.val '' ((Subtype.val : Metric.sphere (0 : Pt d) 1 → Pt d) ⁻¹' capSet a v) =
      capSet a v := by
    refine Set.image_preimage_eq_iff.mpr ?_
    intro u hu
    exact ⟨⟨u, by simp [hu.1]⟩, rfl⟩
  rw [himg]

lemma sphereMeasure_univ_le {d : ℕ} :
    sphereMeasure d Set.univ ≤ (d : ENNReal) * volume (Metric.ball (0 : Pt d) 1) := by
  unfold sphereMeasure
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ]
  rw [Measure.toSphere_apply' volume MeasurableSet.univ, finrank_euclideanSpace_fin,
    Subtype.coe_image_univ]
  have hsub : Set.Ioo (0 : ℝ) 1 • (Metric.sphere (0 : Pt d) 1 : Set (Pt d)) ⊆
      Metric.ball (0 : Pt d) 1 := by
    rintro y ⟨t, ⟨ht0, ht1⟩, u, hu_sp, rfl⟩
    have hu_norm : ‖u‖ = 1 := by simpa using hu_sp
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0,
      hu_norm, mul_one]
    exact ht1
  have hm : volume (Set.Ioo (0 : ℝ) 1 • (Metric.sphere (0 : Pt d) 1 : Set (Pt d))) ≤
      volume (Metric.ball (0 : Pt d) 1) := measure_mono hsub
  gcongr

lemma uniformSphere_cap_ge_of_cone {d : ℕ} (hd : 1 ≤ d) {c₀ a : ℝ}
    {x e₀ : Pt d} (hx : ‖x‖ = 1) (he₀ : ‖e₀‖ = 1)
    (hcone : ENNReal.ofReal c₀ * volume (Metric.ball (0 : Pt d) 1) ≤
      volume (Set.Ioo (0 : ℝ) 1 • capSet a e₀)) :
    ENNReal.ofReal c₀ ≤ uniformSphere d (capSet a x) := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let V : ENNReal := volume (Metric.ball (0 : Pt d) 1)
  have hV_pos : 0 < V := Metric.measure_ball_pos volume 0 zero_lt_one
  have hV_lt_top : V < ⊤ := by
    dsimp [V]
    rw [EuclideanSpace.volume_ball]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top
  have hd_pos : (0 : ENNReal) < (d : ENNReal) := by exact_mod_cast (show 0 < d by omega)
  have hd_lt_top : (d : ENNReal) < ⊤ := ENNReal.natCast_lt_top d
  have hdV_ne_zero : (d : ENNReal) * V ≠ 0 :=
    ne_of_gt (ENNReal.mul_pos (ne_of_gt hd_pos) (ne_of_gt hV_pos))
  have hdV_ne_top : (d : ENNReal) * V ≠ ⊤ := ne_of_lt (ENNReal.mul_lt_top hd_lt_top hV_lt_top)
  have hcone_x : ENNReal.ofReal c₀ * V ≤ volume (Set.Ioo (0 : ℝ) 1 • capSet a x) := by
    rwa [cone_cap_volume_eq a x e₀ hx he₀]
  have hM_le : sphereMeasure d Set.univ ≤ (d : ENNReal) * V := sphereMeasure_univ_le
  have hinv_ge : ((d : ENNReal) * V)⁻¹ ≤ (sphereMeasure d Set.univ)⁻¹ :=
    ENNReal.inv_le_inv.mpr hM_le
  unfold uniformSphere
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [sphereMeasure_cap_eq a x]
  calc ENNReal.ofReal c₀
      = ENNReal.ofReal c₀ * (((d : ENNReal) * V)⁻¹ * ((d : ENNReal) * V)) := by
          rw [ENNReal.inv_mul_cancel hdV_ne_zero hdV_ne_top, mul_one]
    _ = ((d : ENNReal) * V)⁻¹ * ((d : ENNReal) * (ENNReal.ofReal c₀ * V)) := by ring
    _ ≤ (sphereMeasure d Set.univ)⁻¹ *
          ((d : ENNReal) * volume (Set.Ioo (0 : ℝ) 1 • capSet a x)) := by
        gcongr

lemma cone_bound_dim1 {c₀ : ℝ} (hc₀_le : c₀ ≤ 1 / 4) :
    let α : ℝ := 1 + 1 / ((1 : ℕ) : ℝ)
    let ε : ℝ := samplingEps α
    let a : ℝ := 3 * Real.sqrt ε / (2 * Real.sqrt 2)
    let e₀ : Pt 1 := EuclideanSpace.single 0 1
    ‖e₀‖ = 1 ∧
      ENNReal.ofReal c₀ * volume (Metric.ball (0 : Pt 1) 1) ≤
        volume (Set.Ioo (0 : ℝ) 1 • capSet a e₀) := by
  dsimp only
  let e₀ : Pt 1 := EuclideanSpace.single 0 1
  have he₀_norm : ‖e₀‖ = 1 := by simp [e₀]
  refine ⟨he₀_norm, ?_⟩
  set a : ℝ := 3 * Real.sqrt (samplingEps (1 + 1 / ((1 : ℕ) : ℝ))) / (2 * Real.sqrt 2)
  have hε_eq : samplingEps (1 + 1 / ((1 : ℕ) : ℝ)) = 3 / 4 := by
    unfold samplingEps
    norm_num
  have ha_lt1 : a < 1 := by
    have ha_nonneg : 0 ≤ a := by positivity
    have ha_sq : a ^ 2 < 1 ^ 2 := by
      dsimp [a]
      rw [hε_eq, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
      norm_num
    nlinarith
  have he₀_mem : e₀ ∈ capSet a e₀ := by
    refine ⟨he₀_norm, ?_⟩
    rw [real_inner_self_eq_norm_sq, he₀_norm]
    linarith
  have hball_sub : Metric.ball ((1 / 2 : ℝ) • e₀) (1 / 4) ⊆ Set.Ioo (0 : ℝ) 1 • capSet a e₀ := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hnorm_diff : ‖y - (1 / 2 : ℝ) • e₀‖ = |y.ofLp 0 - 1 / 2| := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_one]
      have h0 : (y - (1 / 2 : ℝ) • e₀).ofLp 0 = y.ofLp 0 - 1 / 2 := by
        simp [e₀]
      rw [h0, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
    rw [hnorm_diff, abs_lt] at hy
    refine ⟨y.ofLp 0, ⟨by linarith, by linarith⟩, e₀, he₀_mem, ?_⟩
    ext i
    fin_cases i
    simp [e₀]
  have hvol_ball : volume (Metric.ball ((1 / 2 : ℝ) • e₀) (1 / 4)) =
      ENNReal.ofReal (1 / 4) * volume (Metric.ball (0 : Pt 1) 1) := by
    rw [Measure.addHaar_ball volume ((1 / 2 : ℝ) • e₀) (by norm_num : (0 : ℝ) ≤ 1 / 4),
      finrank_euclideanSpace_fin, pow_one]
  have hc_ofReal : ENNReal.ofReal c₀ ≤ ENNReal.ofReal (1 / 4) := ENNReal.ofReal_le_ofReal hc₀_le
  calc ENNReal.ofReal c₀ * volume (Metric.ball (0 : Pt 1) 1)
      ≤ ENNReal.ofReal (1 / 4) * volume (Metric.ball (0 : Pt 1) 1) := by gcongr
    _ = volume (Metric.ball ((1 / 2 : ℝ) • e₀) (1 / 4)) := hvol_ball.symm
    _ ≤ volume (Set.Ioo (0 : ℝ) 1 • capSet a e₀) := measure_mono hball_sub

lemma gamma_midpoint_ratio (x : ℝ) (hx : 0 < x) :
    Real.sqrt x * Real.Gamma (x + 1 / 2) ≤ Real.Gamma (x + 1) := by
  have hx_mem : x ∈ Set.Ioi (0 : ℝ) := hx
  have hx1_mem : x + 1 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hconv := Real.convexOn_log_Gamma.2 hx_mem hx1_mem
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [Function.comp_apply, smul_eq_mul] at hconv
  have hmid : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * (x + 1) = x + 1 / 2 := by ring
  rw [hmid] at hconv
  have hGx_pos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hGx1_pos : 0 < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hGmid_pos : 0 < Real.Gamma (x + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hlog_sq : Real.log (Real.Gamma (x + 1 / 2) ^ 2) ≤
      Real.log (Real.Gamma x * Real.Gamma (x + 1)) := by
    rw [Real.log_pow, Real.log_mul (ne_of_gt hGx_pos) (ne_of_gt hGx1_pos)]
    push_cast
    linarith
  have hsq_le : Real.Gamma (x + 1 / 2) ^ 2 ≤ Real.Gamma x * Real.Gamma (x + 1) :=
    (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog_sq
  have hrec : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one (ne_of_gt hx)
  have hmul_x : x * Real.Gamma (x + 1 / 2) ^ 2 ≤ Real.Gamma (x + 1) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hsq_le (le_of_lt hx)
    nlinarith [hrec]
  have hlhs_sq : (Real.sqrt x * Real.Gamma (x + 1 / 2)) ^ 2 = x * Real.Gamma (x + 1 / 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hx)]
  rw [← hlhs_sq] at hmul_x
  exact le_of_pow_le_pow_left₀ (by norm_num : 2 ≠ 0) (le_of_lt hGx1_pos) hmul_x

lemma slice_subset_cone {m : ℕ} {a : ℝ} (ha : 0 < a) :
    let e₀ : Pt (m + 1) := EuclideanSpace.single 0 1
    {y : Pt (m + 1) | ‖y‖ < 1 ∧ a ≤ y.ofLp 0} ⊆ Set.Ioo (0 : ℝ) 1 • capSet a e₀ := by
  dsimp only
  rintro y ⟨hy_lt1, hy_a⟩
  let e₀ : Pt (m + 1) := EuclideanSpace.single 0 1
  have hy0_pos : 0 < y.ofLp 0 := lt_of_lt_of_le ha hy_a
  have hy0_le_norm : (y.ofLp 0) ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    have hterm : (y.ofLp 0) ^ 2 = ‖y.ofLp 0‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    rw [hterm]
    exact Finset.single_le_sum (fun i _ => sq_nonneg ‖y.ofLp i‖) (Finset.mem_univ 0)
  have hy_norm_pos : 0 < ‖y‖ := by
    by_contra hle
    have h0 : ‖y‖ = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg y)
    rw [h0] at hy0_le_norm
    nlinarith
  let u : Pt (m + 1) := ‖y‖⁻¹ • y
  have hu_norm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy_norm_pos),
      inv_mul_cancel₀ (ne_of_gt hy_norm_pos)]
  have hu_inner : a < inner ℝ u e₀ := by
    dsimp [u, e₀]
    rw [EuclideanSpace.inner_single_right]
    simp only [starRingEnd_apply, star_trivial, one_mul, PiLp.smul_apply, smul_eq_mul]
    have hinv_gt1 : 1 < ‖y‖⁻¹ := (one_lt_inv₀ hy_norm_pos).mpr hy_lt1
    nlinarith
  refine ⟨‖y‖, ⟨hy_norm_pos, hy_lt1⟩, u, ⟨hu_norm, hu_inner⟩, ?_⟩
  dsimp [u]
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hy_norm_pos), one_smul]

lemma cylinder_volume_le_slice {m : ℕ} {a p q R : ℝ}
    (hp0 : 0 ≤ p) (hap : a ≤ p) (hR0 : 0 ≤ R) (hsum : q ^ 2 + R ^ 2 ≤ 1) :
    ENNReal.ofReal (q - p) * volume (Metric.ball (0 : Pt m) R) ≤
      volume {y : Pt (m + 1) | ‖y‖ < 1 ∧ a ≤ y.ofLp 0} := by
  let f₁ : ℝ × (Fin m → ℝ) → ℝ × Pt m := Prod.map id (WithLp.toLp 2)
  let e_succ : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  let f₂ : ℝ × (Fin m → ℝ) → Pt (m + 1) := (WithLp.toLp 2) ∘ e_succ.symm
  have hf₁ : MeasurePreserving f₁ volume volume :=
    (MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin m))
  have hf₂ : MeasurePreserving f₂ volume volume :=
    (PiLp.volume_preserving_toLp (Fin (m + 1))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
  let Cyl : Set (ℝ × Pt m) := Set.Ioo p q ×ˢ Metric.ball (0 : Pt m) R
  let Slice : Set (Pt (m + 1)) := {y : Pt (m + 1) | ‖y‖ < 1 ∧ a ≤ y.ofLp 0}
  have hCyl_meas : MeasurableSet Cyl := measurableSet_Ioo.prod Metric.isOpen_ball.measurableSet
  have hSlice_meas : MeasurableSet Slice := by
    have heq : Slice = Metric.ball (0 : Pt (m + 1)) 1 ∩ {y : Pt (m + 1) | a ≤ y.ofLp 0} := by
      ext y
      simp [Slice]
    rw [heq]
    have hcont0 : Continuous (fun y : Pt (m + 1) => y.ofLp 0) :=
      PiLp.continuous_apply 2 (fun _ : Fin (m + 1) => ℝ) 0
    exact Metric.isOpen_ball.measurableSet.inter (isClosed_le continuous_const hcont0).measurableSet
  have hsub_pre : f₁ ⁻¹' Cyl ⊆ f₂ ⁻¹' Slice := by
    rintro ⟨t, w⟩ ⟨⟨htp, htq⟩, hwR⟩
    rw [Metric.mem_ball, dist_zero_right] at hwR
    have ht0 : 0 ≤ t := le_trans hp0 (le_of_lt htp)
    have hq_pos : 0 < q := lt_of_le_of_lt ht0 htq
    let z : Fin (m + 1) → ℝ := e_succ.symm (t, w)
    have hz_app : e_succ z = (t, w) := e_succ.apply_symm_apply (t, w)
    have hz0 : z 0 = t := by
      have hfst := congrArg Prod.fst hz_app
      simpa [e_succ, MeasurableEquiv.piFinSuccAbove] using hfst
    have hzsnd : ∀ j : Fin m, z j.succ = w j := by
      intro j
      have hsnd := congrFun (congrArg Prod.snd hz_app) j
      simpa [e_succ, MeasurableEquiv.piFinSuccAbove, Fin.tail] using hsnd
    have hnorm_sq : ‖f₂ (t, w)‖ ^ 2 = t ^ 2 + ‖WithLp.toLp 2 w‖ ^ 2 := by
      dsimp [f₂]
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      change ∑ i : Fin (m + 1), ‖z i‖ ^ 2 = t ^ 2 + ∑ j : Fin m, ‖w j‖ ^ 2
      rw [Fin.sum_univ_succ, hz0, Real.norm_eq_abs, sq_abs]
      have hsum_eq : ∑ j : Fin m, ‖z j.succ‖ ^ 2 = ∑ j : Fin m, ‖w j‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hzsnd j]
      rw [hsum_eq]
    have ht_sq : t ^ 2 < q ^ 2 := (sq_lt_sq₀ ht0 (le_of_lt hq_pos)).mpr htq
    have hw_sq : ‖WithLp.toLp 2 w‖ ^ 2 ≤ R ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hwR) 2
    have hnorm_lt1_sq : ‖f₂ (t, w)‖ ^ 2 < 1 ^ 2 := by linarith
    have hnorm_lt1 : ‖f₂ (t, w)‖ < 1 := lt_of_pow_lt_pow_left₀ 2 zero_le_one hnorm_lt1_sq
    refine ⟨hnorm_lt1, ?_⟩
    change a ≤ z 0
    rw [hz0]
    exact le_trans hap (le_of_lt htp)
  have hvol_cyl : volume Cyl = ENNReal.ofReal (q - p) * volume (Metric.ball (0 : Pt m) R) := by
    change (volume.prod volume) (Set.Ioo p q ×ˢ Metric.ball (0 : Pt m) R) = _
    rw [Measure.prod_prod, Real.volume_Ioo]
  calc ENNReal.ofReal (q - p) * volume (Metric.ball (0 : Pt m) R)
      = volume Cyl := hvol_cyl.symm
    _ = volume (f₁ ⁻¹' Cyl) := (hf₁.measure_preimage hCyl_meas.nullMeasurableSet).symm
    _ ≤ volume (f₂ ⁻¹' Slice) := measure_mono hsub_pre
    _ = volume Slice := hf₂.measure_preimage hSlice_meas.nullMeasurableSet

lemma cone_bound_dim_ge2 (m : ℕ) (hm : 1 ≤ m) :
    let d : ℕ := m + 1
    let α : ℝ := 1 + 1 / (d : ℝ)
    let ε : ℝ := samplingEps α
    let a : ℝ := 3 * Real.sqrt ε / (2 * Real.sqrt 2)
    let e₀ : Pt d := EuclideanSpace.single 0 1
    ‖e₀‖ = 1 ∧
      ENNReal.ofReal (Real.exp (-9) / 60) * volume (Metric.ball (0 : Pt d) 1) ≤
        volume (Set.Ioo (0 : ℝ) 1 • capSet a e₀) := by
  dsimp only
  let d : ℕ := m + 1
  let e₀ : Pt d := EuclideanSpace.single 0 1
  have he₀_norm : ‖e₀‖ = 1 := by simp [e₀]
  refine ⟨he₀_norm, ?_⟩
  have hd_ge2 : 2 ≤ d := by omega
  have hd_real_ge2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_ge2
  have hd_pos : (0 : ℝ) < (d : ℝ) := by linarith
  have hd1_pos : (0 : ℝ) < (d : ℝ) + 1 := by linarith
  obtain ⟨hε_form, hε_pos, _⟩ := samplingEps_formula (show 1 ≤ d by omega)
  set ε : ℝ := samplingEps (1 + 1 / (d : ℝ))
  set a : ℝ := 3 * Real.sqrt ε / (2 * Real.sqrt 2)
  have ha_pos : 0 < a := by positivity
  set p : ℝ := (3 / 2 : ℝ) / Real.sqrt ((d : ℝ) + 1)
  set q : ℝ := (8 / 5 : ℝ) / Real.sqrt ((d : ℝ) + 1)
  have hp_pos : 0 < p := by positivity
  have hap : a ≤ p := by
    have ha_sq : a ^ 2 = 9 * (2 * (d : ℝ) + 1) / (8 * ((d : ℝ) + 1) ^ 2) := by
      dsimp [a]
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (le_of_lt hε_pos),
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hε_form]
      field_simp
      ring
    have hp_sq : p ^ 2 = 9 / (4 * ((d : ℝ) + 1)) := by
      dsimp [p]
      rw [div_pow, Real.sq_sqrt (le_of_lt hd1_pos)]
      field_simp
      ring
    have hsq_le : a ^ 2 ≤ p ^ 2 := by
      rw [ha_sq, hp_sq, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num : 2 ≠ 0) (le_of_lt hp_pos) hsq_le
  have hq_sq_eq : q ^ 2 = (64 / 25 : ℝ) / ((d : ℝ) + 1) := by
    dsimp [q]
    rw [div_pow, Real.sq_sqrt (le_of_lt hd1_pos)]
    field_simp
    ring
  have hq_sq_le : q ^ 2 ≤ 64 / 75 := by
    rw [hq_sq_eq, div_le_iff₀ hd1_pos]
    linarith
  have h1mq_pos : 0 < 1 - q ^ 2 := by linarith
  set R : ℝ := Real.sqrt (1 - q ^ 2)
  have hR_pos : 0 < R := Real.sqrt_pos.mpr h1mq_pos
  have hR_sq : R ^ 2 = 1 - q ^ 2 := Real.sq_sqrt (le_of_lt h1mq_pos)
  have hRm_ge : Real.exp (-9) ≤ R ^ m := by
    have h1mq_ge : (11 / 75 : ℝ) ≤ 1 - q ^ 2 := by linarith
    have hinv_le : (1 - q ^ 2)⁻¹ ≤ Real.exp (18 / ((d : ℝ) + 1)) := by
      have hid : (1 - q ^ 2)⁻¹ = 1 + q ^ 2 / (1 - q ^ 2) := by
        have hne : 1 - q ^ 2 ≠ 0 := ne_of_gt h1mq_pos
        field_simp
        ring
      have hdiv1 : q ^ 2 / (1 - q ^ 2) ≤ (75 / 11 : ℝ) * q ^ 2 := by
        rw [div_le_iff₀ h1mq_pos]
        nlinarith [sq_nonneg q]
      have hdiv2 : (75 / 11 : ℝ) * q ^ 2 ≤ 18 / ((d : ℝ) + 1) := by
        rw [hq_sq_eq]
        have h1 : (75 / 11 : ℝ) * ((64 / 25 : ℝ) / ((d : ℝ) + 1)) =
            (192 / 11 : ℝ) / ((d : ℝ) + 1) := by ring
        rw [h1]
        exact div_le_div_of_nonneg_right (by norm_num) (le_of_lt hd1_pos)
      have hexp1 := Real.add_one_le_exp (18 / ((d : ℝ) + 1))
      linarith
    have hexp_neg_le : Real.exp (-(18 / ((d : ℝ) + 1))) ≤ R ^ 2 := by
      rw [Real.exp_neg, hR_sq]
      exact (inv_le_comm₀ h1mq_pos (Real.exp_pos _)).mp hinv_le
    have hpow_m : (Real.exp (-(18 / ((d : ℝ) + 1)))) ^ m ≤ (R ^ 2) ^ m :=
      pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hexp_neg_le m
    rw [← Real.exp_nat_mul] at hpow_m
    have hm_le_d1 : (m : ℝ) ≤ (d : ℝ) + 1 := by
      have hmd : (d : ℝ) = (m : ℝ) + 1 := by exact_mod_cast (rfl : d = m + 1)
      linarith
    have hexp_m18 : Real.exp (-18) ≤ Real.exp ((m : ℝ) * -(18 / ((d : ℝ) + 1))) := by
      refine Real.exp_le_exp.mpr ?_
      have hmul_le : (m : ℝ) * (18 / ((d : ℝ) + 1)) ≤ 18 := by
        rw [← mul_div_assoc, div_le_iff₀ hd1_pos]
        linarith
      linarith
    have hsq_final : (Real.exp (-9)) ^ 2 ≤ (R ^ m) ^ 2 := by
      have he9 : (Real.exp (-9)) ^ 2 = Real.exp (-18) := by
        rw [← Real.exp_nat_mul]
        norm_num
      have hR2m : (R ^ 2) ^ m = (R ^ m) ^ 2 := by ring
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num : 2 ≠ 0) (by positivity) hsq_final
  have hcyl_le_cone : ENNReal.ofReal (q - p) * volume (Metric.ball (0 : Pt m) R) ≤
      volume (Set.Ioo (0 : ℝ) 1 • capSet a e₀) :=
    le_trans (cylinder_volume_le_slice (le_of_lt hp_pos) hap (le_of_lt hR_pos) (by linarith))
      (measure_mono (slice_subset_cone ha_pos))
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin d) := ⟨0⟩
  have hvol_m : volume (Metric.ball (0 : Pt m) R) =
      ENNReal.ofReal (R ^ m * (Real.sqrt Real.pi ^ m / Real.Gamma ((m : ℝ) / 2 + 1))) := by
    rw [EuclideanSpace.volume_ball, Fintype.card_fin,
      ← ENNReal.ofReal_pow (le_of_lt hR_pos) m, ← ENNReal.ofReal_mul (by positivity)]
  have hvol_d : volume (Metric.ball (0 : Pt d) 1) =
      ENNReal.ofReal (Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1)) := by
    rw [EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  have hqp_eq : q - p = (1 / 10 : ℝ) / Real.sqrt ((d : ℝ) + 1) := by
    dsimp [p, q]
    ring
  have hqp_pos : 0 < q - p := by
    rw [hqp_eq]
    positivity
  rw [hvol_d, ← ENNReal.ofReal_mul (by positivity)]
  rw [hvol_m, ← ENNReal.ofReal_mul (le_of_lt hqp_pos)] at hcyl_le_cone
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hcyl_le_cone
  have hGm_pos : 0 < Real.Gamma ((m : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hGd_pos : 0 < Real.Gamma ((d : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hmid_eq : (m : ℝ) / 2 + 1 = (d : ℝ) / 2 + 1 / 2 := by
    have hmd : (d : ℝ) = (m : ℝ) + 1 := by exact_mod_cast (rfl : d = m + 1)
    linarith
  have hgamma : Real.sqrt ((d : ℝ) / 2) * Real.Gamma ((m : ℝ) / 2 + 1) ≤
      Real.Gamma ((d : ℝ) / 2 + 1) := by
    rw [hmid_eq]
    exact gamma_midpoint_ratio ((d : ℝ) / 2) (by positivity)
  have hpi_bound : Real.sqrt Real.pi ≤ 6 * (Real.sqrt ((d : ℝ) / 2) / Real.sqrt ((d : ℝ) + 1)) := by
    have hrhs_pos : 0 < 6 * (Real.sqrt ((d : ℝ) / 2) / Real.sqrt ((d : ℝ) + 1)) := by positivity
    have hsq : (Real.sqrt Real.pi) ^ 2 ≤
        (6 * (Real.sqrt ((d : ℝ) / 2) / Real.sqrt ((d : ℝ) + 1))) ^ 2 := by
      rw [Real.sq_sqrt (le_of_lt Real.pi_pos), mul_pow, div_pow,
        Real.sq_sqrt (by positivity), Real.sq_sqrt (le_of_lt hd1_pos)]
      have h12 : (4 : ℝ) ≤ 36 * (((d : ℝ) / 2) / ((d : ℝ) + 1)) := by
        rw [ div_eq_mul_inv, ← mul_assoc, ← div_eq_mul_inv, le_div_iff₀ hd1_pos]
        linarith
      linarith [Real.pi_lt_four]
    exact le_of_pow_le_pow_left₀ (by norm_num : 2 ≠ 0) (le_of_lt hrhs_pos) hsq
  have hpow_pi : Real.sqrt Real.pi ^ d = Real.sqrt Real.pi ^ m * Real.sqrt Real.pi := by
    change Real.sqrt Real.pi ^ (m + 1) = _
    rw [pow_succ]
  rw [hpow_pi, hqp_eq]
  have hpi_m_pos : 0 < Real.sqrt Real.pi ^ m := pow_pos (Real.sqrt_pos.mpr Real.pi_pos) m
  have hcore : (Real.exp (-9) / 60) * (Real.sqrt Real.pi / Real.Gamma ((d : ℝ) / 2 + 1)) ≤
      ((1 / 10 : ℝ) / Real.sqrt ((d : ℝ) + 1)) * (R ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) := by
    rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ hGd_pos hGm_pos]
    have h1 : Real.sqrt Real.pi * Real.Gamma ((m : ℝ) / 2 + 1) ≤
        6 * (Real.sqrt ((d : ℝ) / 2) * Real.Gamma ((m : ℝ) / 2 + 1)) / Real.sqrt ((d : ℝ) + 1) := by
      have hm1 := mul_le_mul_of_nonneg_right hpi_bound (le_of_lt hGm_pos)
      calc Real.sqrt Real.pi * Real.Gamma ((m : ℝ) / 2 + 1)
          ≤ 6 * (Real.sqrt ((d : ℝ) / 2) / Real.sqrt ((d : ℝ) + 1)) *
              Real.Gamma ((m : ℝ) / 2 + 1) := hm1
        _ = 6 * (Real.sqrt ((d : ℝ) / 2) * Real.Gamma ((m : ℝ) / 2 + 1)) /
              Real.sqrt ((d : ℝ) + 1) := by ring
    have h2 : 6 * (Real.sqrt ((d : ℝ) / 2) * Real.Gamma ((m : ℝ) / 2 + 1)) /
          Real.sqrt ((d : ℝ) + 1) ≤
        6 * Real.Gamma ((d : ℝ) / 2 + 1) / Real.sqrt ((d : ℝ) + 1) := by
      gcongr
    have h3 : (Real.exp (-9) / 60) * (Real.sqrt Real.pi * Real.Gamma ((m : ℝ) / 2 + 1)) ≤
        ((1 / 10 : ℝ) / Real.sqrt ((d : ℝ) + 1)) * Real.exp (-9) * Real.Gamma ((d : ℝ) / 2 + 1) := by
      have hm2 := mul_le_mul_of_nonneg_left (le_trans h1 h2) (by positivity : 0 ≤ Real.exp (-9) / 60)
      calc (Real.exp (-9) / 60) * (Real.sqrt Real.pi * Real.Gamma ((m : ℝ) / 2 + 1))
          ≤ (Real.exp (-9) / 60) * (6 * Real.Gamma ((d : ℝ) / 2 + 1) / Real.sqrt ((d : ℝ) + 1)) := hm2
        _ = ((1 / 10 : ℝ) / Real.sqrt ((d : ℝ) + 1)) * Real.exp (-9) *
              Real.Gamma ((d : ℝ) / 2 + 1) := by ring
    have h4 : ((1 / 10 : ℝ) / Real.sqrt ((d : ℝ) + 1)) * Real.exp (-9) *
          Real.Gamma ((d : ℝ) / 2 + 1) ≤
        ((1 / 10 : ℝ) / Real.sqrt ((d : ℝ) + 1)) * R ^ m * Real.Gamma ((d : ℝ) / 2 + 1) := by
      gcongr
    calc (Real.exp (-9) / 60 * Real.sqrt Real.pi) * Real.Gamma ((m : ℝ) / 2 + 1)
        = (Real.exp (-9) / 60) * (Real.sqrt Real.pi * Real.Gamma ((m : ℝ) / 2 + 1)) := by ring
      _ ≤ ((1 / 10 : ℝ) / Real.sqrt ((d : ℝ) + 1)) * R ^ m * Real.Gamma ((d : ℝ) / 2 + 1) :=
          le_trans h3 h4
      _ = ((1 / 10 : ℝ) / Real.sqrt ((d : ℝ) + 1) * R ^ m) * Real.Gamma ((d : ℝ) / 2 + 1) := by ring
  have hm_scale := mul_le_mul_of_nonneg_right hcore (le_of_lt hpi_m_pos)
  calc Real.exp (-9) / 60 *
        ((Real.sqrt Real.pi ^ m * Real.sqrt Real.pi) / Real.Gamma ((d : ℝ) / 2 + 1))
      = ((Real.exp (-9) / 60) * (Real.sqrt Real.pi / Real.Gamma ((d : ℝ) / 2 + 1))) *
          Real.sqrt Real.pi ^ m := by ring
    _ ≤ (((1 / 10 : ℝ) / Real.sqrt ((d : ℝ) + 1)) * (R ^ m / Real.Gamma ((m : ℝ) / 2 + 1))) *
          Real.sqrt Real.pi ^ m := hm_scale
    _ = (1 / 10 : ℝ) / Real.sqrt ((d : ℝ) + 1) *
          (R ^ m * (Real.sqrt Real.pi ^ m / Real.Gamma ((m : ℝ) / 2 + 1))) := by ring

end AuxLemma41

theorem solution : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (s t : Pt d) (r₀ : ℝ), s ≠ t → 0 < r₀ →
    r₀ ≤ dist s t → dist s t ≤ 2 * r₀ →
    ENNReal.ofReal c₀ ≤ uniformSphere d {u : Pt d |
      Covers (1 + 1 / (d : ℝ)) s (s + (r₀ * Real.sqrt (2 * samplingEps (1 + 1 / (d : ℝ)))) • u) t} := by
  let c₀ : ℝ := Real.exp (-9) / 60
  have hc₀_pos : 0 < c₀ := by positivity
  refine ⟨c₀, hc₀_pos, ?_⟩
  intro d hd s t r₀ hst hr₀ hlo hhi
  obtain ⟨hx_norm, hcap_sub⟩ := AuxLemma41.cap_subset_covers hd s t r₀ hst hr₀ hlo hhi
  refine le_trans ?_ (measure_mono hcap_sub)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hd
  by_cases hm0 : m = 0
  · subst hm0
    have hc₀_le : c₀ ≤ 1 / 4 := by
      dsimp [c₀]
      have he9 : Real.exp (-9) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      linarith
    obtain ⟨he₀_norm, hcone1⟩ := AuxLemma41.cone_bound_dim1 hc₀_le
    exact AuxLemma41.uniformSphere_cap_ge_of_cone (by omega) hx_norm he₀_norm hcone1
  · have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
    obtain ⟨he₀_norm, hcone2⟩ := AuxLemma41.cone_bound_dim_ge2 m hm1
    exact AuxLemma41.uniformSphere_cap_ge_of_cone (by omega) hx_norm he₀_norm hcone2

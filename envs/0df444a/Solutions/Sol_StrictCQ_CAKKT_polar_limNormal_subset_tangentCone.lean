-- Prove2me | solution 1 for StrictCQ.CAKKT.polar_limNormal_subset_tangentCone
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:55:12.698599+00:00
-- url     : https://prove2.me/submissions/1fb5f73e-5161-47f9-9349-44d5def804b3

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting

open Filter Topology Set
open scoped InnerProductSpace
open StrictCQ.CAKKT

/-- Proximal normals are regular normals. -/
lemma cakkt_proximal_regNormal {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {w p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ S) (hmin : ∀ q ∈ S, ‖w - p‖ ≤ ‖w - q‖) :
    w - p ∈ regNormal S p := by
  refine ⟨hp, fun ε hε => ?_⟩
  have hb : Metric.ball p (2 * ε) ∈ 𝓝 p := Metric.ball_mem_nhds p (by linarith)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hb] with q hq hqb
  have h1 := hmin q hq
  have h2 : ‖w - p‖ ^ 2 ≤ ‖w - q‖ ^ 2 := by gcongr
  have h3 : w - q = (w - p) - (q - p) := by abel
  rw [h3, norm_sub_sq_real (w - p) (q - p)] at h2
  have h4 : ‖q - p‖ < 2 * ε := by rw [← dist_eq_norm]; exact hqb
  have h5 : ‖q - p‖ ^ 2 ≤ 2 * ε * ‖q - p‖ := by
    rw [sq]; exact mul_le_mul_of_nonneg_right h4.le (norm_nonneg _)
  nlinarith

lemma cakkt_regNormal_smul {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {p v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ regNormal S p) {c : ℝ} (hc : 0 < c) :
    c • v ∈ regNormal S p := by
  refine ⟨hv.1, fun ε hε => ?_⟩
  filter_upwards [hv.2 (ε / c) (div_pos hε hc)] with y hy
  rw [real_inner_smul_left]
  calc c * ⟪v, y - p⟫_ℝ ≤ c * (ε / c * ‖y - p‖) := by gcongr
    _ = ε * ‖y - p‖ := by field_simp

theorem solution {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : IsClosed S) {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ S) :
    StrictCQ.AGP.polar (limNormal S z) ⊆ tangentCone S z := by
  intro d hd
  -- Step 1: uniform bound on regular normals near `z`.
  have hunif : ∀ ε > (0:ℝ), ∃ ρ > (0:ℝ), ∀ p ∈ S, dist p z < ρ →
      ∀ v ∈ regNormal S p, ⟪d, v⟫_ℝ ≤ ε * ‖v‖ := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    have hseq : ∀ k : ℕ, ∃ p ∈ S, dist p z < 1 / ((k:ℝ) + 1) ∧
        ∃ v ∈ regNormal S p, ε * ‖v‖ < ⟪d, v⟫_ℝ := fun k => hcon _ (by positivity)
    choose p hpS hpd v hvN hvi using hseq
    have hv0 : ∀ k, 0 < ‖v k‖ := by
      intro k
      rcases eq_or_ne (v k) 0 with h | h
      · have := hvi k; simp [h] at this
      · exact norm_pos_iff.2 h
    set u : ℕ → EuclideanSpace ℝ (Fin n) := fun k => ‖v k‖⁻¹ • v k with hu
    have hus : ∀ k, u k ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      intro k; simp [hu, norm_smul, (hv0 k).ne']
    obtain ⟨u0, -, φ, hφ, hlim⟩ :=
      (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).tendsto_subseq hus
    have hpz : Tendsto p atTop (𝓝 z) := by
      refine tendsto_iff_dist_tendsto_zero.2 ?_
      exact squeeze_zero (fun _ => dist_nonneg) (fun k => (hpd k).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hu0 : u0 ∈ limNormal S z :=
      ⟨p ∘ φ, u ∘ φ, fun k => hpS _, hpz.comp hφ.tendsto_atTop, hlim,
        fun k => cakkt_regNormal_smul (hvN (φ k)) (inv_pos.2 (hv0 _))⟩
    have h1 := hd u0 hu0
    have h2 : ε ≤ ⟪d, u0⟫_ℝ := by
      refine ge_of_tendsto (tendsto_const_nhds.inner hlim) (Eventually.of_forall fun k => ?_)
      simp only [Function.comp, hu, inner_smul_right]
      have := hvi (φ k)
      have hp := hv0 (φ k)
      calc ε = ‖v (φ k)‖⁻¹ * (ε * ‖v (φ k)‖) := by field_simp
        _ ≤ ‖v (φ k)‖⁻¹ * ⟪d, v (φ k)⟫_ℝ := by gcongr
    linarith
  -- Step 2: the distance function along the ray grows slowly.
  set f : ℝ → ℝ := fun t => Metric.infDist (z + t • d) S with hf
  have hfc : Continuous f :=
    (Metric.continuous_infDist_pt S).comp (continuous_const.add (continuous_id.smul continuous_const))
  have hf0 : f 0 = 0 := by simp [hf, Metric.infDist_zero_of_mem hz]
  have hfLip : ∀ x h, f (x + h) ≤ f x + |h| * ‖d‖ := by
    intro x h
    have := Metric.infDist_le_infDist_add_dist (x := z + (x + h) • d) (y := z + x • d) (s := S)
    simp only [hf]
    have e : dist (z + (x + h) • d) (z + x • d) = |h| * ‖d‖ := by
      rw [dist_eq_norm, add_smul]
      simp [norm_smul]
    linarith
  have hgrow : ∀ ε > (0:ℝ), ∃ T > (0:ℝ), ∀ t ∈ Icc (0:ℝ) T, f t ≤ 2 * ε * t := by
    intro ε hε
    obtain ⟨ρ, hρ, hρb⟩ := hunif ε hε
    set T := ρ / (2 * ‖d‖ + 1) with hT
    have hTpos : 0 < T := by positivity
    have hT2 : 2 * T * ‖d‖ < ρ := by
      rw [hT]
      have : 0 < 2 * ‖d‖ + 1 := by positivity
      have h1 : ρ * (2 * ‖d‖ / (2 * ‖d‖ + 1)) < ρ := by
        apply mul_lt_of_lt_one_right hρ
        rw [div_lt_one this]; linarith
      calc 2 * (ρ / (2 * ‖d‖ + 1)) * ‖d‖ = ρ * (2 * ‖d‖ / (2 * ‖d‖ + 1)) := by ring
        _ < ρ := h1
    refine ⟨T, hTpos, fun t ht => ?_⟩
    have key : ∀ β > (0:ℝ), f t ≤ 2 * ε * t + β := by
      intro β hβ
      set f' : ℝ → ℝ := fun x => if 0 < f x then ε else ‖d‖ with hf'
      refine image_le_of_liminf_slope_right_lt_deriv_boundary (f := f) (f' := f')
        (B := fun x => 2 * ε * x + β) (B' := fun _ => 2 * ε) hfc.continuousOn ?_ ?_ ?_ ?_ ht
      · intro x hx r hr
        apply Filter.Eventually.frequently
        by_cases hfx : 0 < f x
        · simp only [hf', hfx, if_true] at hr
          -- nearest point
          obtain ⟨q, hqS, hq⟩ := hS.exists_infDist_eq_dist ⟨z, hz⟩ (z + x • d)
          set w := z + x • d with hw
          have hfx' : f x = ‖w - q‖ := by rw [hf]; simp only; rw [hq, dist_eq_norm]
          have hfxle : f x ≤ x * ‖d‖ := by
            have := Metric.infDist_le_dist_of_mem (x := w) hz
            rw [dist_eq_norm, hw] at this
            simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg hx.1] at this
            exact this
          have hqz : dist q z < ρ := by
            rw [dist_eq_norm]
            have : q - z = (w - z) - (w - q) := by abel
            rw [this]
            calc ‖(w - z) - (w - q)‖ ≤ ‖w - z‖ + ‖w - q‖ := norm_sub_le _ _
              _ = x * ‖d‖ + f x := by
                rw [hfx', hw]; simp [norm_smul, abs_of_nonneg hx.1]
              _ ≤ 2 * T * ‖d‖ := by
                have := hx.2.le
                nlinarith [norm_nonneg d]
              _ < ρ := hT2
          have hmin : ∀ q' ∈ S, ‖w - q‖ ≤ ‖w - q'‖ := by
            intro q' hq'
            rw [← dist_eq_norm, ← dist_eq_norm, ← hq]
            exact Metric.infDist_le_dist_of_mem hq'
          have hN := hρb q hqS hqz (w - q) (cakkt_proximal_regNormal hqS hmin)
          rw [← hfx'] at hN
          have hev : ∀ᶠ h in 𝓝[>] (0:ℝ), h * ‖d‖ ^ 2 < 2 * (r - ε) * f x := by
            have : Tendsto (fun h : ℝ => h * ‖d‖ ^ 2) (𝓝[>] 0) (𝓝 (0 * ‖d‖ ^ 2)) :=
              (tendsto_id.mul tendsto_const_nhds).mono_left nhdsWithin_le_nhds
            rw [zero_mul] at this
            exact this.eventually (gt_mem_nhds (by have := sub_pos.2 hr; positivity))
          have hev2 : ∀ᶠ y in 𝓝[>] x, (y - x) * ‖d‖ ^ 2 < 2 * (r - ε) * f x ∧ x < y := by
            have ht : Tendsto (fun y => y - x) (𝓝[>] x) (𝓝[>] 0) := by
              rw [tendsto_nhdsWithin_iff]
              refine ⟨?_, ?_⟩
              · have : Tendsto (fun y => y - x) (𝓝 x) (𝓝 (x - x)) :=
                  tendsto_id.sub tendsto_const_nhds
                rw [sub_self] at this
                exact this.mono_left nhdsWithin_le_nhds
              · filter_upwards [self_mem_nhdsWithin] with y hy
                exact sub_pos.2 (show x < y from hy)
            exact (ht.eventually hev).and self_mem_nhdsWithin
          filter_upwards [hev2] with y ⟨hy1, hy2⟩
          set h := y - x with hh
          have hpos : 0 < h := sub_pos.2 hy2
          rw [slope_def_field, div_lt_iff₀ (sub_pos.2 hy2)]
          have hfy : f y ≤ ‖(w - q) + h • d‖ := by
            have := Metric.infDist_le_dist_of_mem (x := z + y • d) hqS
            rw [dist_eq_norm] at this
            have e : z + y • d - q = (w - q) + h • d := by
              rw [hw, hh, sub_smul]; abel
            rw [e] at this; exact this
          have hsq : ‖(w - q) + h • d‖ ^ 2 < (f x + h * r) ^ 2 := by
            rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
              abs_of_pos hpos, ← hfx', real_inner_comm]
            have : ⟪d, w - q⟫_ℝ ≤ ε * f x := hN
            have i1 := mul_lt_mul_of_pos_left hy1 hpos
            have i2 := mul_le_mul_of_nonneg_left this hpos.le
            nlinarith [sq_nonneg (h * r)]
          have hlt : ‖(w - q) + h • d‖ < f x + h * r :=
            lt_of_pow_lt_pow_left₀ 2 (by nlinarith [sub_pos.2 hr]) hsq
          linarith
        · simp only [hf', hfx, if_false] at hr
          filter_upwards [self_mem_nhdsWithin] with y hy
          have hy' : 0 < y - x := sub_pos.2 hy
          rw [slope_def_field, div_lt_iff₀ hy']
          have := hfLip x (y - x)
          rw [add_sub_cancel, abs_of_pos hy'] at this
          nlinarith
      · simp [hf0, hβ.le]
      · intro x; simpa using ((hasDerivAt_id x).const_mul (2 * ε)).add_const β
      · intro x hx hfx
        have hpos : 0 < f x := by
          rw [hfx]; have := hx.1; positivity
        simp only [hf', hpos, if_true]
        linarith
    by_contra hcon
    push Not at hcon
    have := key ((f t - 2 * ε * t) / 2) (by linarith)
    linarith
  -- Step 3: build the tangent sequence.
  have hsel : ∀ k : ℕ, ∃ t : ℝ, 0 < t ∧ t ≤ 1 / ((k:ℝ) + 1) ∧ f t ≤ 2 * (1 / ((k:ℝ) + 1)) * t := by
    intro k
    obtain ⟨T, hT, hTb⟩ := hgrow (1 / ((k:ℝ) + 1)) (by positivity)
    refine ⟨min T (1 / ((k:ℝ) + 1)), lt_min hT (by positivity), min_le_right _ _, ?_⟩
    exact hTb _ ⟨(lt_min hT (by positivity)).le, min_le_left _ _⟩
  choose t ht0 ht1 ht2 using hsel
  have hnp : ∀ k, ∃ q ∈ S, Metric.infDist (z + t k • d) S = dist (z + t k • d) q :=
    fun k => hS.exists_infDist_eq_dist ⟨z, hz⟩ _
  choose q hqS hq using hnp
  have hinv : Tendsto (fun k : ℕ => 1 / ((k:ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨t, fun k => (t k)⁻¹ • (q k - z), ht0, ?_, ?_, fun k => ?_⟩
  · exact squeeze_zero (fun k => (ht0 k).le) ht1 hinv
  · refine tendsto_iff_dist_tendsto_zero.2 ?_
    have hb : ∀ k, dist ((t k)⁻¹ • (q k - z)) d ≤ 2 * (1 / ((k:ℝ) + 1)) := by
      intro k
      have e : (t k)⁻¹ • (q k - z) - d = (t k)⁻¹ • (q k - (z + t k • d)) := by
        rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ (ht0 k).ne', one_smul]
        abel
      rw [dist_eq_norm, e, norm_smul, norm_sub_rev, ← dist_eq_norm, ← hq k, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 (ht0 k))]
      have := ht2 k
      simp only [hf] at this
      rw [inv_mul_le_iff₀ (ht0 k)]
      linarith
    have h2 : Tendsto (fun k : ℕ => 2 * (1 / ((k:ℝ) + 1))) atTop (𝓝 0) := by
      simpa using hinv.const_mul 2
    exact squeeze_zero (fun _ => dist_nonneg) hb h2
  · rw [smul_smul, mul_inv_cancel₀ (ht0 k).ne', one_smul, add_sub_cancel]
    exact hqS k

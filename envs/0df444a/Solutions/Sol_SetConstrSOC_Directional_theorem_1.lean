-- Prove2me | solution 1 for SetConstrSOC.Directional.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:43:59.672412+00:00
-- url     : https://prove2.me/submissions/01504003-be9e-40de-8461-ef26ac4afda5

import Mathlib
import Definitions.Def_SetConstrSOC_Directional_Model

set_option autoImplicit false
open Filter Asymptotics
open scoped Topology
open SetConstrSOC.Directional

theorem taylor2_aux {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (G : E → F) (hG : ContDiff ℝ 2 G) (x : E)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r > 0, ∀ h : E, ‖h‖ ≤ r →
      ‖G (x + h) - G x - fderiv ℝ G x h - (1 / 2 : ℝ) • (fderiv ℝ (fderiv ℝ G) x h) h‖
        ≤ ε * ‖h‖ ^ 2 := by
  have hG1 : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hdG : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  have hD : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x :=
    ((hdG.differentiable (by norm_num)) x).hasFDerivAt
  have hlo := hD.isLittleO
  rw [Asymptotics.isLittleO_iff] at hlo
  have hev := hlo hε
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨r / 2, by positivity, fun h hh => ?_⟩
  set B := fderiv ℝ (fderiv ℝ G) x with hB
  let ψ : ℝ → F := fun s => G (x + s • h) - s • (fderiv ℝ G x h) - (s ^ 2 / 2) • (B h h)
  let ψ' : ℝ → F := fun s => fderiv ℝ G (x + s • h) h - fderiv ℝ G x h - s • (B h h)
  have hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt ψ (ψ' s) (Set.Icc 0 1) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => x + s • h) h s := by
      simpa using ((hasDerivAt_id s).smul_const h).const_add x
    have h2 : HasDerivAt (fun s : ℝ => G (x + s • h)) (fderiv ℝ G (x + s • h) h) s :=
      (hG1 (x + s • h)).hasFDerivAt.comp_hasDerivAt s h1
    have h3 : HasDerivAt (fun s : ℝ => s • (fderiv ℝ G x h)) (fderiv ℝ G x h) s := by
      simpa using (hasDerivAt_id s).smul_const (fderiv ℝ G x h)
    have h4 : HasDerivAt (fun s : ℝ => (s ^ 2 / 2) • (B h h)) (s • (B h h)) s := by
      have : HasDerivAt (fun s : ℝ => s ^ 2 / 2) s s := by
        simpa using ((hasDerivAt_pow 2 s).div_const 2)
      simpa using this.smul_const (B h h)
    exact ((h2.sub h3).sub h4).hasDerivWithinAt
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖ψ' s‖ ≤ ε * ‖h‖ ^ 2 := by
    intro s hs
    have hsn : ‖s • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hs.2
    have hmem : x + s • h ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm]; simp only [add_sub_cancel_left]; linarith
    have := hball (x + s • h) hmem
    simp only [add_sub_cancel_left] at this
    have e : ψ' s = (fderiv ℝ G (x + s • h) - fderiv ℝ G x - B (s • h)) h := by
      simp only [ψ', ContinuousLinearMap.sub_apply, map_smul, ContinuousLinearMap.smul_apply]
    rw [e]
    calc ‖(fderiv ℝ G (x + s • h) - fderiv ℝ G x - B (s • h)) h‖
        ≤ ‖fderiv ℝ G (x + s • h) - fderiv ℝ G x - B (s • h)‖ * ‖h‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (ε * ‖s • h‖) * ‖h‖ := by gcongr
      _ ≤ (ε * ‖h‖) * ‖h‖ := by gcongr
      _ = ε * ‖h‖ ^ 2 := by ring
  have key := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
  have e1 : ψ 1 - ψ 0 = G (x + h) - G x - fderiv ℝ G x h - (1 / 2 : ℝ) • (B h h) := by
    simp only [ψ]; simp
    abel_nf
  simpa [e1] using key

theorem taylor2_littleO {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (G : E → F) (hG : ContDiff ℝ 2 G) (x : E) :
    (fun h : E => G (x + h) - G x - fderiv ℝ G x h - (1 / 2 : ℝ) • (fderiv ℝ (fderiv ℝ G) x h) h)
      =o[𝓝 0] (fun h : E => ‖h‖ ^ 2) := by
  rw [isLittleO_iff]
  intro c hc
  obtain ⟨r, hr, hh⟩ := taylor2_aux G hG x c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨r, hr, fun h hd => ?_⟩
  have : ‖h‖ ≤ r := by simpa [dist_eq_norm] using hd.le
  simpa using hh h this

theorem taylor_expand {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (G : E → F) (hG : ContDiff ℝ 2 G) (x d w : E)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) (wk : ℕ → E) (hw : Tendsto wk atTop (𝓝 w)) :
    (fun k => G (x + t k • d + ((1 / 2 : ℝ) * (t k) ^ 2) • wk k) -
        (G x + t k • fderiv ℝ G x d + ((1 / 2 : ℝ) * (t k) ^ 2) •
          (fderiv ℝ G x (wk k) + (fderiv ℝ (fderiv ℝ G) x d) d)))
      =o[atTop] (fun k => (t k) ^ 2) := by
  set B := fderiv ℝ (fderiv ℝ G) x with hB
  set h : ℕ → E := fun k => t k • d + ((1 / 2 : ℝ) * (t k) ^ 2) • wk k with hhdef
  have hh0 : Tendsto h atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => t k • d) atTop (𝓝 ((0:ℝ) • d)) := ht.smul_const d
    have h2 : Tendsto (fun k => ((1 / 2 : ℝ) * (t k) ^ 2) • wk k) atTop
        (𝓝 (((1 / 2 : ℝ) * (0:ℝ) ^ 2) • w)) :=
      (((ht.pow 2).const_mul (1 / 2 : ℝ))).smul hw
    rw [hhdef]
    simpa using h1.add h2
  have hR := (taylor2_littleO G hG x).comp_tendsto hh0
  have hwb : ∀ᶠ k in atTop, ‖wk k‖ ≤ ‖w‖ + 1 := by
    have := (hw.norm).eventually (gt_mem_nhds (lt_add_one ‖w‖))
    exact this.mono fun k hk => hk.le
  have ht1 : ∀ᶠ k in atTop, |t k| ≤ 1 := by
    have := ht.eventually (Metric.closedBall_mem_nhds (0:ℝ) one_pos)
    exact this.mono fun k hk => by simpa [Real.dist_eq] using hk
  set W := ‖w‖ + 1 with hW
  have hW0 : 0 ≤ W := by positivity
  have hbig : (fun k => ‖h k‖ ^ 2) =O[atTop] (fun k => (t k) ^ 2) := by
    refine IsBigO.of_bound ((‖d‖ + W) ^ 2) ?_
    filter_upwards [hwb, ht1] with k hk1 hk2
    have e1 : ‖h k‖ ≤ |t k| * (‖d‖ + W) := by
      calc ‖h k‖ ≤ ‖t k • d‖ + ‖((1 / 2 : ℝ) * (t k) ^ 2) • wk k‖ := norm_add_le _ _
        _ = |t k| * ‖d‖ + (1 / 2 * (t k) ^ 2) * ‖wk k‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / 2 * (t k) ^ 2)]
        _ ≤ |t k| * ‖d‖ + |t k| * W := by
          have : (1 / 2 * (t k) ^ 2) * ‖wk k‖ ≤ |t k| * W := by
            have a1 : 1 / 2 * (t k) ^ 2 ≤ |t k| := by
              have : (t k) ^ 2 = |t k| ^ 2 := (sq_abs _).symm
              rw [this]; nlinarith [abs_nonneg (t k)]
            calc (1 / 2 * (t k) ^ 2) * ‖wk k‖ ≤ |t k| * ‖wk k‖ :=
                  mul_le_mul_of_nonneg_right a1 (norm_nonneg _)
              _ ≤ |t k| * W := mul_le_mul_of_nonneg_left hk1 (abs_nonneg _)
          linarith
        _ = |t k| * (‖d‖ + W) := by ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    calc ‖h k‖ ^ 2 ≤ (|t k| * (‖d‖ + W)) ^ 2 := by gcongr
      _ = (‖d‖ + W) ^ 2 * (t k) ^ 2 := by rw [mul_pow, sq_abs]; ring
  have hR2 := hR.trans_isBigO hbig
  -- cross term
  have hP : (fun k => (1 / 2 : ℝ) • (B (h k) (h k) - ((t k) ^ 2) • B d d))
      =O[atTop] (fun k => (t k) ^ 3) := by
    refine IsBigO.of_bound (‖B‖ * (2 * (‖d‖ * W) + W ^ 2)) ?_
    filter_upwards [hwb, ht1] with k hk1 hk2
    set s : ℝ := (1 / 2 : ℝ) * (t k) ^ 2 with hs
    have hexp : B (h k) (h k) - ((t k) ^ 2) • B d d =
        (t k * s) • (B d (wk k) + B (wk k) d) + (s ^ 2) • B (wk k) (wk k) := by
      simp only [hhdef, map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, hs]
      module
    have hu := abs_nonneg (t k)
    set u := |t k| with hu_def
    have hsu : s = u ^ 2 / 2 := by rw [hs, hu_def, sq_abs]; ring
    have hs0 : 0 ≤ s := by positivity
    have n1 : ‖B d (wk k)‖ ≤ ‖B‖ * ‖d‖ * W :=
      (ContinuousLinearMap.le_opNorm₂ _ _ _).trans (by gcongr)
    have n2 : ‖B (wk k) d‖ ≤ ‖B‖ * W * ‖d‖ :=
      (ContinuousLinearMap.le_opNorm₂ _ _ _).trans (by gcongr)
    have n3 : ‖B (wk k) (wk k)‖ ≤ ‖B‖ * W * W :=
      (ContinuousLinearMap.le_opNorm₂ _ _ _).trans (by gcongr)
    have a3 : ‖B d (wk k) + B (wk k) d‖ ≤ ‖B‖ * ‖d‖ * W + ‖B‖ * W * ‖d‖ :=
      (norm_add_le _ _).trans (add_le_add n1 n2)
    have key : ‖(t k * s) • (B d (wk k) + B (wk k) d) + (s ^ 2) • B (wk k) (wk k)‖ ≤
        u ^ 3 * (‖B‖ * (2 * (‖d‖ * W) + W ^ 2)) := by
      calc _ ≤ ‖(t k * s) • (B d (wk k) + B (wk k) d)‖ + ‖(s ^ 2) • B (wk k) (wk k)‖ :=
            norm_add_le _ _
        _ = |t k * s| * ‖B d (wk k) + B (wk k) d‖ + |s ^ 2| * ‖B (wk k) (wk k)‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ = (u ^ 3 / 2) * ‖B d (wk k) + B (wk k) d‖ + (u ^ 4 / 4) * ‖B (wk k) (wk k)‖ := by
            rw [abs_mul, abs_of_nonneg hs0, abs_of_nonneg (by positivity : 0 ≤ s ^ 2), hsu]
            ring
        _ ≤ (u ^ 3 / 2) * (‖B‖ * ‖d‖ * W + ‖B‖ * W * ‖d‖) + (u ^ 3 / 4) * (‖B‖ * W * W) := by
            have : u ^ 4 ≤ u ^ 3 := pow_le_pow_of_le_one hu hk2 (by norm_num)
            gcongr
        _ ≤ _ := by
            have hBn := norm_nonneg B
            have hdn := norm_nonneg d
            have h3 : 0 ≤ u ^ 3 := by positivity
            have h4 : 0 ≤ ‖B‖ * ‖d‖ * W := by positivity
            have h5 : 0 ≤ ‖B‖ * W * W := by positivity
            nlinarith [mul_nonneg h3 h4, mul_nonneg h3 h5]
    rw [norm_smul, Real.norm_eq_abs, hexp, Real.norm_eq_abs, abs_pow]
    have h3 : 0 ≤ u ^ 3 * (‖B‖ * (2 * (‖d‖ * W) + W ^ 2)) := by positivity
    rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    nlinarith
  have h3 : (fun k => (t k) ^ 3) =o[atTop] (fun k => (t k) ^ 2) :=
    (isLittleO_pow_pow (by norm_num : 2 < 3)).comp_tendsto ht
  have hP2 := hP.trans_isLittleO h3
  have := hR2.add hP2
  refine this.congr_left (fun k => ?_)
  simp only [hhdef, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_sub, smul_add, Function.comp_apply, hB]
  rw [← add_assoc x]
  module


theorem scsd_dirNbhd {n : ℕ} (d w : E n) (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), t • d + ((1 / 2 : ℝ) * t ^ 2) • w ∈ dirNbhd ρ δ d := by
  have hn := norm_nonneg d
  have hw := norm_nonneg w
  -- first condition
  have S1 : ∀ᶠ t in 𝓝[>] (0:ℝ), ‖t • d + ((1 / 2 : ℝ) * t ^ 2) • w‖ ≤ ρ := by
    have hpos : (0:ℝ) < min 1 (ρ / (‖d‖ + ‖w‖ + 1)) := lt_min one_pos (by positivity)
    filter_upwards [Ioo_mem_nhdsGT hpos] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h1 : t ≤ 1 := ht1.le.trans (min_le_left _ _)
    have h2 : t ≤ ρ / (‖d‖ + ‖w‖ + 1) := ht1.le.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h2
    calc ‖t • d + ((1 / 2 : ℝ) * t ^ 2) • w‖
        ≤ ‖t • d‖ + ‖((1 / 2 : ℝ) * t ^ 2) • w‖ := norm_add_le _ _
      _ = t * ‖d‖ + (1 / 2 * t ^ 2) * ‖w‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht0,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / 2 * t ^ 2)]
      _ ≤ t * ‖d‖ + t * ‖w‖ := by
          have : 1 / 2 * t ^ 2 ≤ t := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right this hw]
      _ ≤ ρ := by nlinarith
  have S2 : ∀ᶠ t in 𝓝[>] (0:ℝ), ‖‖d‖ • (t • d + ((1 / 2 : ℝ) * t ^ 2) • w) -
      ‖t • d + ((1 / 2 : ℝ) * t ^ 2) • w‖ • d‖ ≤
        δ * ‖t • d + ((1 / 2 : ℝ) * t ^ 2) • w‖ * ‖d‖ := by
    by_cases hd : d = 0
    · subst hd
      exact Filter.Eventually.of_forall fun t => by simp
    · have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd
      have hpos : (0:ℝ) < ‖d‖ * min 1 (δ / 2) / (‖w‖ + 1) := by positivity
      filter_upwards [Ioo_mem_nhdsGT hpos] with t ht
      obtain ⟨ht0, ht1⟩ := ht
      rw [lt_div_iff₀ (by positivity)] at ht1
      have hA : t * ‖w‖ ≤ ‖d‖ := by
        have : min 1 (δ / 2) ≤ 1 := min_le_left _ _
        nlinarith [mul_le_mul_of_nonneg_left this hdn.le]
      have hB : t * ‖w‖ ≤ δ * ‖d‖ / 2 := by
        have : min 1 (δ / 2) ≤ δ / 2 := min_le_right _ _
        nlinarith [mul_le_mul_of_nonneg_left this hdn.le]
      set s : ℝ := (1 / 2 : ℝ) * t ^ 2 with hs
      have hs0 : 0 ≤ s := by positivity
      set h := t • d + s • w with hh
      have e1 : ‖d‖ • h - ‖h‖ • d = (t * ‖d‖ - ‖h‖) • d + (s * ‖d‖) • w := by
        simp only [hh, smul_add, smul_smul]; module
      have e2 : |t * ‖d‖ - ‖h‖| ≤ s * ‖w‖ := by
        have : ‖t • d‖ = t * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
        have h3 := abs_norm_sub_norm_le (t • d) h
        rw [this] at h3
        have h4 : ‖t • d - h‖ = s * ‖w‖ := by
          have : t • d - h = -(s • w) := by simp only [hh]; abel
          rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
        linarith
      have e3 : ‖‖d‖ • h - ‖h‖ • d‖ ≤ 2 * s * ‖w‖ * ‖d‖ := by
        rw [e1]
        calc _ ≤ ‖(t * ‖d‖ - ‖h‖) • d‖ + ‖(s * ‖d‖) • w‖ := norm_add_le _ _
          _ = |t * ‖d‖ - ‖h‖| * ‖d‖ + (s * ‖d‖) * ‖w‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg (by positivity : 0 ≤ s * ‖d‖)]
          _ ≤ s * ‖w‖ * ‖d‖ + (s * ‖d‖) * ‖w‖ := by gcongr
          _ = 2 * s * ‖w‖ * ‖d‖ := by ring
      have e4 : t * ‖d‖ / 2 ≤ ‖h‖ := by
        have hn1 : ‖t • d‖ = t * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
        have h3 := abs_norm_sub_norm_le (t • d) h
        have h4 : ‖t • d - h‖ = s * ‖w‖ := by
          have : t • d - h = -(s • w) := by simp only [hh]; abel
          rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
        have h5 : s * ‖w‖ ≤ t * ‖d‖ / 2 := by
          have : s * ‖w‖ = t / 2 * (t * ‖w‖) := by rw [hs]; ring
          rw [this]; nlinarith
        have h6 := (abs_le.mp h3).2
        rw [hn1, h4] at h6
        linarith
      calc ‖‖d‖ • h - ‖h‖ • d‖ ≤ 2 * s * ‖w‖ * ‖d‖ := e3
        _ = t * (t * ‖w‖) * ‖d‖ := by rw [hs]; ring
        _ ≤ t * (δ * ‖d‖ / 2) * ‖d‖ := by gcongr
        _ = δ * (t * ‖d‖ / 2) * ‖d‖ := by ring
        _ ≤ δ * ‖h‖ * ‖d‖ := by gcongr
  filter_upwards [S1, S2] with t h1 h2
  exact ⟨h1, h2⟩


theorem scsd_foexp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (G : E → F) (x : E)
    (hG : DifferentiableAt ℝ G x) (d : E)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) (dk : ℕ → E) (hd : Tendsto dk atTop (𝓝 d)) :
    (fun k => G (x + t k • dk k) - G x - t k • fderiv ℝ G x (dk k)) =o[atTop] t := by
  set h : ℕ → E := fun k => t k • dk k with hhdef
  have hh0 : Tendsto h atTop (𝓝 0) := by
    simpa using ht.smul hd
  have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hG.hasFDerivAt).comp_tendsto hh0
  have hbig : h =O[atTop] t := by
    refine IsBigO.of_bound (‖d‖ + 1) ?_
    have hb : ∀ᶠ k in atTop, ‖dk k‖ ≤ ‖d‖ + 1 := by
      have := (hd.norm).eventually (gt_mem_nhds (lt_add_one ‖d‖))
      exact this.mono fun k hk => hk.le
    filter_upwards [hb] with k hk
    simp only [hhdef, norm_smul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hk (norm_nonneg _) |>.trans_eq (by ring) |>.trans_eq rfl
  have := hlo.trans_isBigO hbig
  refine this.congr_left (fun k => ?_)
  simp [hhdef]

theorem scsd_tangent_fwd {n m : ℕ} (g : E n → E m) (Λ : Set (E m)) (hg : ContDiff ℝ 2 g)
    (x d : E n) (hx : g x ∈ Λ) (hd : d ∈ tangentCone {y | g y ∈ Λ} x) :
    (fderiv ℝ g x) d ∈ tangentCone Λ (g x) := by
  obtain ⟨-, t, dk, ht0, htt, hdk, hmem⟩ := hd
  have hgd : DifferentiableAt ℝ g x := (hg.differentiable (by norm_num)) x
  refine ⟨hx, t, fun k => (t k)⁻¹ • (g (x + t k • dk k) - g x), ht0, htt, ?_, ?_⟩
  · have h1 := (scsd_foexp g x hgd d t htt dk hdk).tendsto_inv_smul_nhds_zero
    have h2 : Tendsto (fun k => (fderiv ℝ g x) (dk k)) atTop (𝓝 ((fderiv ℝ g x) d)) :=
      ((fderiv ℝ g x).continuous.tendsto d).comp hdk
    have h3 := h2.add h1
    simp only [add_zero] at h3
    refine h3.congr (fun k => ?_)
    have : t k ≠ 0 := (ht0 k).ne'
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ this, one_smul]
    abel
  · intro k
    have : t k ≠ 0 := (ht0 k).ne'
    simpa [smul_smul, mul_inv_cancel₀ this] using hmem k


theorem scsd_tangent_bwd {n m : ℕ} (g : E n → E m) (Λ : Set (E m)) (hg : ContDiff ℝ 2 g)
    (x d : E n) (κ : ℝ) (hMS : MetricSubregularDir g Λ x d κ)
    (hd : (fderiv ℝ g x) d ∈ tangentCone Λ (g x)) :
    d ∈ tangentCone {y | g y ∈ Λ} x := by
  obtain ⟨hgx, hκ, ρ, hρ, δ, hδ, hms⟩ := hMS
  obtain ⟨-, t, u, ht0, htt, hu, hmem⟩ := hd
  have hgd : DifferentiableAt ℝ g x := (hg.differentiable (by norm_num)) x
  set F : Set (E n) := {y | g y ∈ Λ} with hF
  have hFne : F.Nonempty := ⟨x, hgx⟩
  have hy : ∀ k, ∃ y ∈ F, dist (x + t k • d) y < Metric.infDist (x + t k • d) F + (t k) ^ 2 :=
    fun k => (Metric.infDist_lt_iff hFne).mp (by have := pow_pos (ht0 k) 2; linarith)
  choose y hyF hyd using hy
  refine ⟨hgx, t, fun k => (t k)⁻¹ • (y k - x), ht0, htt, ?_, ?_⟩
  swap
  · intro k
    have : t k ≠ 0 := (ht0 k).ne'
    simpa [smul_smul, mul_inv_cancel₀ this] using hyF k
  have htn : Tendsto t atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨htt, Eventually.of_forall ht0⟩
  have hnb := htn.eventually (scsd_dirNbhd d 0 ρ δ hρ hδ)
  have hlo := scsd_foexp g x hgd d t htt (fun _ => d) tendsto_const_nhds
  have ha : Tendsto (fun k => ‖g (x + t k • d) - g x - t k • fderiv ℝ g x d‖ / t k)
      atTop (𝓝 0) := by
    have := hlo.norm_left
    have h2 := this.tendsto_div_nhds_zero
    refine h2.congr (fun k => ?_)
    simp [abs_of_pos (ht0 k)]
  have hb : Tendsto (fun k => ‖fderiv ℝ g x d - u k‖) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := fderiv ℝ g x d)).sub hu
    simpa using this.norm
  have hup : Tendsto (fun k => κ * (‖g (x + t k • d) - g x - t k • fderiv ℝ g x d‖ / t k +
      ‖fderiv ℝ g x d - u k‖) + t k) atTop (𝓝 0) := by
    simpa using ((ha.add hb).const_mul κ).add htt
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hup
  filter_upwards [hnb] with k hk
  have htk := ht0 k
  have hk' : t k • d + ((1 / 2 : ℝ) * (t k) ^ 2) • (0 : E n) ∈ dirNbhd ρ δ d := hk
  rw [smul_zero, add_zero] at hk'
  have h1 := hms _ hk'
  have h2 : Metric.infDist (g (x + t k • d)) Λ ≤
      ‖g (x + t k • d) - g x - t k • fderiv ℝ g x d‖ + t k * ‖fderiv ℝ g x d - u k‖ := by
    have := Metric.infDist_le_dist_of_mem (x := g (x + t k • d)) (hmem k)
    rw [dist_eq_norm] at this
    refine this.trans ?_
    have e : g (x + t k • d) - (g x + t k • u k) =
        (g (x + t k • d) - g x - t k • fderiv ℝ g x d) + t k • (fderiv ℝ g x d - u k) := by
      module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htk]
  have h3 : ‖(t k)⁻¹ • (y k - x) - d‖ ≤ (t k)⁻¹ * (Metric.infDist (x + t k • d) F + (t k) ^ 2) := by
    have e : (t k)⁻¹ • (y k - x) - d = (t k)⁻¹ • (y k - (x + t k • d)) := by
      rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ htk.ne']
      module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htk)]
    apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr htk).le
    have := (hyd k).le
    rw [dist_comm, dist_eq_norm] at this
    exact this
  calc ‖(t k)⁻¹ • (y k - x) - d‖
      ≤ (t k)⁻¹ * (Metric.infDist (x + t k • d) F + (t k) ^ 2) := h3
    _ ≤ (t k)⁻¹ * (κ * (‖g (x + t k • d) - g x - t k • fderiv ℝ g x d‖ +
          t k * ‖fderiv ℝ g x d - u k‖) + (t k) ^ 2) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = κ * (‖g (x + t k • d) - g x - t k • fderiv ℝ g x d‖ / t k +
          ‖fderiv ℝ g x d - u k‖) + t k := by
        field_simp


theorem scsd_nonneg {n : ℕ} (f : E n → ℝ) (S : Set (E n)) (hf : ContDiff ℝ 2 f) (x : E n)
    (hmin : IsLocalMinOn f S x) (d : E n) (hd : d ∈ tangentCone S x) :
    0 ≤ fderiv ℝ f x d := by
  obtain ⟨hxS, t, dk, ht0, htt, hdk, hmem⟩ := hd
  have hfd : DifferentiableAt ℝ f x := (hf.differentiable (by norm_num)) x
  have hlo := scsd_foexp f x hfd d t htt dk hdk
  have hx0 : Tendsto (fun k => x + t k • dk k) atTop (𝓝[S] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hmem⟩
    simpa using tendsto_const_nhds.add (htt.smul hdk)
  have hev : ∀ᶠ k in atTop, f x ≤ f (x + t k • dk k) := hx0.eventually hmin
  by_contra hneg0
  have hneg : fderiv ℝ f x d < 0 := not_le.mp hneg0
  set c := fderiv ℝ f x d with hc
  have hcont : Tendsto (fun k => fderiv ℝ f x (dk k)) atTop (𝓝 c) :=
    ((fderiv ℝ f x).continuous.tendsto d).comp hdk
  have h1 : ∀ᶠ k in atTop, fderiv ℝ f x (dk k) < c / 2 :=
    hcont.eventually (gt_mem_nhds (by linarith))
  have h2 := hlo.def (by linarith : 0 < -c / 4)
  obtain ⟨k, hk, hk1, hk2⟩ := (hev.and (h1.and h2)).exists
  have htk := ht0 k
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos htk] at hk2
  have := (abs_le.mp hk2).2
  simp only [smul_eq_mul] at this
  nlinarith [mul_lt_mul_of_pos_left hk1 htk]


theorem solution {n m : ℕ} (P : Problem n m) (hP : P.Standing)
    (x : E n) (hmin : IsLocalMinOn P.f P.feasible x) (hx : x ∈ P.feasible)
    (d : E n) (hd : d ∈ tangentCone P.feasible x)
    (hzero : (fderiv ℝ P.f x) d = 0) :
    ∀ w ∈ secondOrderTangentSet P.feasible x d,
      0 ≤ (fderiv ℝ P.f x) w + ((fderiv ℝ (fderiv ℝ P.f) x) d) d := by
  obtain ⟨hf, -, -⟩ := hP
  intro w hw
  obtain ⟨-, t, wk, ht0, htt, hwk, hmem⟩ := hw
  have hexp := taylor_expand P.f hf x d w t htt wk hwk
  have hx0 : Tendsto (fun k => x + t k • d + ((1 / 2 : ℝ) * (t k) ^ 2) • wk k) atTop
      (𝓝[P.feasible] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hmem⟩
    have h1 : Tendsto (fun k => t k • d) atTop (𝓝 ((0:ℝ) • d)) := htt.smul_const d
    have h2 : Tendsto (fun k => ((1 / 2 : ℝ) * (t k) ^ 2) • wk k) atTop
        (𝓝 (((1 / 2 : ℝ) * (0:ℝ) ^ 2) • w)) :=
      (((htt.pow 2).const_mul (1 / 2 : ℝ))).smul hwk
    simpa [add_assoc] using (tendsto_const_nhds (x := x)).add (h1.add h2)
  have hev : ∀ᶠ k in atTop, P.f x ≤ P.f (x + t k • d + ((1 / 2 : ℝ) * (t k) ^ 2) • wk k) :=
    hx0.eventually hmin
  by_contra hneg0
  have hneg := not_le.mp hneg0
  set L := (fderiv ℝ P.f x) w + ((fderiv ℝ (fderiv ℝ P.f) x) d) d with hL
  have hcont : Tendsto (fun k => (fderiv ℝ P.f x) (wk k) + ((fderiv ℝ (fderiv ℝ P.f) x) d) d)
      atTop (𝓝 L) :=
    (((fderiv ℝ P.f x).continuous.tendsto w).comp hwk).add_const _
  have h1 : ∀ᶠ k in atTop,
      (fderiv ℝ P.f x) (wk k) + ((fderiv ℝ (fderiv ℝ P.f) x) d) d < L / 2 :=
    hcont.eventually (gt_mem_nhds (by linarith))
  have h2 := hexp.def (by linarith : 0 < -L / 8)
  obtain ⟨k, hk, hk1, hk2⟩ := (hev.and (h1.and h2)).exists
  have htk := ht0 k
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos htk 2)] at hk2
  have := (abs_le.mp hk2).2
  simp only [smul_eq_mul, hzero, mul_zero, add_zero] at this
  have hp := pow_pos htk 2
  nlinarith [mul_lt_mul_of_pos_left hk1 hp]


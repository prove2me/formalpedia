-- Prove2me | solution 1 for SetConstrSOC.Directional.lemma_3_14
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:54:08.963708+00:00
-- url     : https://prove2.me/submissions/5828ce66-e28b-4a49-9a79-e85dc098bae2

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


theorem scsd_prox {n : ℕ} (S : Set (E n)) (p y : E n) (hp : p ∈ S)
    (hmin : ∀ s ∈ S, dist y p ≤ dist y s) (c : ℝ) (hc : 0 ≤ c) :
    c • (y - p) ∈ regNormal S p := by
  refine ⟨hp, fun ε hε => ?_⟩
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨2 * ε / (c + 1), by positivity, fun s hs hsS => ?_⟩
  have h1 := hmin s hsS
  rw [dist_eq_norm, dist_eq_norm] at h1
  have h2 : ‖y - p‖ ^ 2 ≤ ‖y - s‖ ^ 2 := by gcongr
  have e : y - s = (y - p) - (s - p) := by abel
  have h2' := norm_sub_sq_real (y - p) (s - p)
  rw [e] at h2
  have h3 : 2 * inner ℝ (y - p) (s - p) ≤ ‖s - p‖ ^ 2 := by linarith
  have h4 : ‖s - p‖ ≤ 2 * ε / (c + 1) := by
    have := hs; rw [dist_eq_norm] at this; exact this.le
  rw [inner_smul_left]
  simp only [conj_trivial]
  have h5 : c * ‖s - p‖ ≤ 2 * ε := by
    have : ‖s - p‖ * (c + 1) ≤ 2 * ε := by
      rwa [le_div_iff₀ (by positivity)] at h4
    nlinarith [norm_nonneg (s - p)]
  have hn := norm_nonneg (s - p)
  nlinarith [mul_nonneg hc hn, mul_le_mul_of_nonneg_right h5 hn]


theorem scsd_stepA {n : ℕ} (S : Set (E n)) (hS : IsClosed S) (x d w v : E n) (hx : x ∈ S)
    (hw : w ∈ secondOrderTangentSet S x d)
    (hv : v ∈ regNormal (secondOrderTangentSet S x d) w) :
    ∀ ε > 0, ∃ t : ℝ, ∃ d' v' : E n, 0 < t ∧ t < ε ∧ ‖d' - d‖ < ε ∧ ‖v' - v‖ < ε ∧
      v' ∈ regNormal S (x + t • d') := by
  intro ε hε
  set T := secondOrderTangentSet S x d with hT
  obtain ⟨-, t, wk, ht0, htt, hwk, hmem⟩ := hw
  obtain ⟨-, hreg⟩ := hv
  have hreg' := hreg (ε / 4) (by positivity)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hreg'
  obtain ⟨r, hr, hr'⟩ := hreg'
  set τ : ℝ := r / (4 * (‖v‖ + 1)) with hτdef
  have hv0 := norm_nonneg v
  have hτ : 0 < τ := by positivity
  have hτv : 2 * τ * ‖v‖ < r := by
    have : τ * (4 * (‖v‖ + 1)) = r := by rw [hτdef]; field_simp
    nlinarith
  have hSne : S.Nonempty := ⟨x, hx⟩
  set Yk : ℕ → E n := fun k => x + t k • d + ((1 / 2 : ℝ) * (t k) ^ 2) • (wk k + τ • v) with hYk
  have hP : ∀ k, ∃ P ∈ S, Metric.infDist (Yk k) S = dist (Yk k) P :=
    fun k => hS.exists_infDist_eq_dist hSne _
  choose P hPS hPd using hP
  set pk : ℕ → E n := fun k => (2 / (t k) ^ 2) • (P k - (x + t k • d)) with hpk
  have F1 : ∀ k, x + t k • d + ((1 / 2 : ℝ) * (t k) ^ 2) • pk k = P k := by
    intro k
    have : t k ≠ 0 := (ht0 k).ne'
    simp only [hpk, smul_smul]
    have h1 : (1 / 2 : ℝ) * (t k) ^ 2 * (2 / (t k) ^ 2) = 1 := by field_simp
    rw [h1, one_smul]; abel
  have F2 : ∀ k, ‖pk k - (wk k + τ • v)‖ ≤ τ * ‖v‖ := by
    intro k
    have htk := ht0 k
    have hz := hmem k
    have h1 : dist (Yk k) (P k) ≤ dist (Yk k) (x + t k • d + ((1 / 2 : ℝ) * (t k) ^ 2) • wk k) := by
      rw [← hPd k]; exact Metric.infDist_le_dist_of_mem hz
    have e1 : Yk k - (x + t k • d + ((1 / 2 : ℝ) * (t k) ^ 2) • wk k) =
        ((1 / 2 : ℝ) * (t k) ^ 2) • (τ • v) := by simp only [hYk]; module
    have e2 : Yk k - P k = ((1 / 2 : ℝ) * (t k) ^ 2) • ((wk k + τ • v) - pk k) := by
      rw [← F1 k]; simp only [hYk]; module
    rw [dist_eq_norm, dist_eq_norm, e1, e2, norm_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity), norm_smul, Real.norm_eq_abs, abs_of_pos hτ] at h1
    have h2 : ‖(wk k + τ • v) - pk k‖ ≤ τ * ‖v‖ := by
      have hh : 0 < (1 / 2 : ℝ) * (t k) ^ 2 := by positivity
      have := (mul_le_mul_iff_of_pos_left hh).mp h1
      exact this
    rwa [norm_sub_rev] at h2
  have F3 : ∀ k, τ⁻¹ • (wk k + τ • v - pk k) ∈ regNormal S (P k) := by
    intro k
    have htk := ht0 k
    have := scsd_prox S (P k) (Yk k) (hPS k) (fun s hs => by
      rw [← hPd k]; exact Metric.infDist_le_dist_of_mem hs) (2 / ((t k) ^ 2 * τ)) (by positivity)
    have e2 : Yk k - P k = ((1 / 2 : ℝ) * (t k) ^ 2) • ((wk k + τ • v) - pk k) := by
      rw [← F1 k]; simp only [hYk]; module
    rw [e2, smul_smul] at this
    have h1 : 2 / ((t k) ^ 2 * τ) * ((1 / 2 : ℝ) * (t k) ^ 2) = τ⁻¹ := by
      field_simp
    rwa [h1] at this
  -- bounded subsequence
  have hbd : ∃ᶠ k in atTop, pk k ∈ Metric.closedBall w (2 * τ * ‖v‖ + 1) := by
    have h1 : ∀ᶠ k in atTop, ‖wk k - w‖ < 1 := by
      have := (tendsto_iff_norm_sub_tendsto_zero.mp hwk).eventually (gt_mem_nhds one_pos)
      exact this
    refine (h1.mono fun k hk => ?_).frequently
    rw [Metric.mem_closedBall, dist_eq_norm]
    have := F2 k
    have e : pk k - w = (pk k - (wk k + τ • v)) + (wk k - w) + τ • v := by abel
    rw [e]
    calc ‖(pk k - (wk k + τ • v)) + (wk k - w) + τ • v‖
        ≤ ‖pk k - (wk k + τ • v)‖ + ‖wk k - w‖ + ‖τ • v‖ := norm_add₃_le
      _ ≤ τ * ‖v‖ + 1 + τ * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ]; linarith
      _ = 2 * τ * ‖v‖ + 1 := by ring
  obtain ⟨pb, -, φ, hφ, hpb⟩ :=
    tendsto_subseq_of_frequently_bounded Metric.isBounded_closedBall hbd
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hpbT : pb ∈ T := ⟨hx, t ∘ φ, pk ∘ φ, fun k => ht0 _, htt.comp hφt, hpb,
    fun k => by
      show x + t (φ k) • d + ((1 / 2 : ℝ) * (t (φ k)) ^ 2) • pk (φ k) ∈ S
      rw [F1 (φ k)]; exact hPS (φ k)⟩
  have hwφ : Tendsto (wk ∘ φ) atTop (𝓝 w) := hwk.comp hφt
  have hball : ‖pb - (w + τ • v)‖ ≤ τ * ‖v‖ := by
    have h1 : Tendsto (fun k => ‖(pk ∘ φ) k - ((wk ∘ φ) k + τ • v)‖) atTop
        (𝓝 ‖pb - (w + τ • v)‖) := (hpb.sub (hwφ.add_const _)).norm
    exact le_of_tendsto' h1 (fun k => F2 (φ k))
  have hpw : ‖pb - w‖ < r := by
    have : pb - w = (pb - (w + τ • v)) + τ • v := by abel
    rw [this]
    calc ‖(pb - (w + τ • v)) + τ • v‖ ≤ ‖pb - (w + τ • v)‖ + ‖τ • v‖ := norm_add_le _ _
      _ ≤ τ * ‖v‖ + τ * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ]; linarith
      _ < r := by linarith
  have hreg2 := hr' (y := pb) (by rwa [dist_eq_norm]) hpbT
  have hsmall : ‖pb - w‖ ≤ τ * ε / 2 := by
    set u := pb - w with hu
    have h1 : ‖u - τ • v‖ ^ 2 ≤ (τ * ‖v‖) ^ 2 := by
      have e : u - τ • v = pb - (w + τ • v) := by simp only [hu]; abel
      rw [e]; gcongr
    have h2 := norm_sub_sq_real u (τ • v)
    rw [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hτ] at h2
    have h3 : inner ℝ v u = inner ℝ u v := real_inner_comm _ _
    have h4 : inner ℝ v u ≤ ε / 4 * ‖u‖ := hreg2
    have hun := norm_nonneg u
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [mul_pos hτ hε, mul_nonneg hun hun]
  -- choose k
  have c1 : ∀ᶠ k in atTop, t (φ k) < ε := (htt.comp hφt).eventually (gt_mem_nhds hε)
  have c2 : ∀ᶠ k in atTop, ‖wk (φ k) - w‖ < τ * ε / 4 :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hwφ).eventually (gt_mem_nhds (by positivity))
  have c3 : ∀ᶠ k in atTop, ‖pk (φ k) - pb‖ < min (τ * ε / 4) 1 :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hpb).eventually
      (gt_mem_nhds (lt_min (by positivity) one_pos))
  have c4 : ∀ᶠ k in atTop, (1 / 2 : ℝ) * t (φ k) * (‖pb‖ + 1) < ε := by
    have : Tendsto (fun k => (1 / 2 : ℝ) * t (φ k) * (‖pb‖ + 1)) atTop
        (𝓝 ((1 / 2 : ℝ) * 0 * (‖pb‖ + 1))) :=
      (((htt.comp hφt).const_mul (1 / 2 : ℝ))).mul_const _
    rw [mul_zero, zero_mul] at this
    exact this.eventually (gt_mem_nhds hε)
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := (c1.and (c2.and (c3.and c4))).exists
  have hk3a := lt_of_lt_of_le hk3 (min_le_left _ _)
  have hk3b := lt_of_lt_of_le hk3 (min_le_right _ _)
  have htk := ht0 (φ k)
  refine ⟨t (φ k), d + ((1 / 2 : ℝ) * t (φ k)) • pk (φ k),
    τ⁻¹ • (wk (φ k) + τ • v - pk (φ k)), htk, hk1, ?_, ?_, ?_⟩
  · rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : ‖pk (φ k)‖ ≤ ‖pb‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (pk (φ k)) pb
      linarith
    calc (1 / 2 : ℝ) * t (φ k) * ‖pk (φ k)‖ ≤ (1 / 2 : ℝ) * t (φ k) * (‖pb‖ + 1) := by gcongr
      _ < ε := hk4
  · have e : τ⁻¹ • (wk (φ k) + τ • v - pk (φ k)) - v = τ⁻¹ • (wk (φ k) - pk (φ k)) := by
      rw [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hτ.ne', one_smul]; module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
    have : ‖wk (φ k) - pk (φ k)‖ < τ * ε := by
      have e2 : wk (φ k) - pk (φ k) = (wk (φ k) - w) - (pb - w) - (pk (φ k) - pb) := by abel
      rw [e2]
      calc ‖(wk (φ k) - w) - (pb - w) - (pk (φ k) - pb)‖
          ≤ ‖wk (φ k) - w‖ + ‖pb - w‖ + ‖pk (φ k) - pb‖ := by
            refine (norm_sub_le _ _).trans ?_
            gcongr
            exact norm_sub_le _ _
        _ < τ * ε := by linarith
    calc τ⁻¹ * ‖wk (φ k) - pk (φ k)‖ < τ⁻¹ * (τ * ε) := by gcongr
      _ = ε := by field_simp
  · have := F3 (φ k)
    have e : P (φ k) = x + t (φ k) • (d + ((1 / 2 : ℝ) * t (φ k)) • pk (φ k)) := by
      calc P (φ k) = x + t (φ k) • d + ((1 / 2 : ℝ) * (t (φ k)) ^ 2) • pk (φ k) := (F1 _).symm
        _ = _ := by module
    rwa [e] at this


theorem solution {n : ℕ} (S : Set (E n)) (hS : IsClosed S)
    (x d w : E n) (hx : x ∈ S) (hd : d ∈ tangentCone S x)
    (hw : w ∈ secondOrderTangentSet S x d) :
    limNormal (secondOrderTangentSet S x d) w ⊆ dirLimNormal S x d := by
  intro v hv
  obtain ⟨-, wj, vj, hwj, hvj, hreg⟩ := hv
  refine ⟨hx, ?_⟩
  have key : ∀ ε > 0, ∃ t : ℝ, ∃ d' v' : E n, 0 < t ∧ t < ε ∧ ‖d' - d‖ < ε ∧ ‖v' - v‖ < ε ∧
      v' ∈ regNormal S (x + t • d') := by
    intro ε hε
    have h1 : ∀ᶠ j in atTop, ‖vj j - v‖ < ε / 2 :=
      (tendsto_iff_norm_sub_tendsto_zero.mp hvj).eventually (gt_mem_nhds (by positivity))
    obtain ⟨j, hj⟩ := h1.exists
    obtain ⟨t, d', v', h1, h2, h3, h4, h5⟩ :=
      scsd_stepA S hS x d (wj j) (vj j) hx (hreg j).1 (hreg j) (ε / 2) (by positivity)
    refine ⟨t, d', v', h1, by linarith, by linarith, ?_, h5⟩
    calc ‖v' - v‖ = ‖(v' - vj j) + (vj j - v)‖ := by congr 1; abel
      _ ≤ ‖v' - vj j‖ + ‖vj j - v‖ := norm_add_le _ _
      _ < ε := by linarith
  choose tj dj vj' h1 h2 h3 h4 h5 using fun j : ℕ => key (1 / ((j : ℝ) + 1)) (by positivity)
  refine ⟨tj, dj, vj', h1, ?_, ?_, ?_, h5⟩
  · exact squeeze_zero (fun j => (h1 j).le) (fun j => (h2 j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun j => norm_nonneg _) (fun j => (h3 j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun j => norm_nonneg _) (fun j => (h4 j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat


-- Prove2me | solution 1 for Subamenable.EpiDiff.pwlq_lsc_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T23:48:29.615067+00:00
-- url     : https://prove2.me/submissions/4a1a50f6-2aa9-4b4a-8e99-aba4c9849f49

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite

open Filter Topology Subamenable.EpiDiff
open scoped InnerProductSpace

lemma SA48_poly_closed {m : ℕ} {C : Set (E m)} (hC : IsPolyhedral C) : IsClosed C := by
  obtain ⟨k, c, b, rfl⟩ := hC
  rw [Set.setOf_forall]
  exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const

lemma SA48_piece_val {m : ℕ} (θ : E m → EReal) (R : PWLQRep m) (hrep : IsPWLQRep θ R)
    (j : Fin R.s) {y0 w : E m} (t : ℝ) (h0 : y0 ∈ R.Omega j)
    (h1 : y0 + t • w ∈ R.Omega j) :
    θ (y0 + t • w) = (((θ y0).toReal + t * ⟪R.A j y0 + R.a j, w⟫_ℝ +
      t ^ 2 / 2 * ⟪R.A j w, w⟫_ℝ : ℝ) : EReal) := by
  rw [hrep.2.2.2 j _ h1, hrep.2.2.2 j _ h0, EReal.toReal_coe]
  congr 1
  have hsym : ⟪R.A j w, y0⟫_ℝ = ⟪R.A j y0, w⟫_ℝ := by
    have := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (hrep.2.1 j)) w y0
    exact this.trans (real_inner_comm _ _)
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real, hsym]
  ring

lemma SAL_poly_convex {m : ℕ} {C : Set (E m)} (hC : IsPolyhedral C) : Convex ℝ C := by
  obtain ⟨k, c, b, rfl⟩ := hC
  intro x hx y hy a b' ha hb hab j
  have h1 := hx j
  have h2 := hy j
  simp only [inner_add_right, inner_smul_right]
  have e : b j = a * b j + b' * b j := by rw [← add_mul, hab, one_mul]
  rw [e]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

lemma SAL_chord {m : ℕ} (θ : E m → EReal) (hbot : ∀ y, θ y ≠ ⊥)
    (hcv : Convex ℝ {p : E m × ℝ | θ p.1 ≤ (p.2 : EReal)}) {y z : E m}
    (hy : θ y ≠ ⊤) (hz : θ z ≠ ⊤) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    θ (y + s • (z - y)) ≤ (((1 - s) * (θ y).toReal + s * (θ z).toReal : ℝ) : EReal) := by
  have hya : θ y = ((θ y).toReal : EReal) := (EReal.coe_toReal hy (hbot y)).symm
  have hzb : θ z = ((θ z).toReal : EReal) := (EReal.coe_toReal hz (hbot z)).symm
  have hmem := hcv (x := (y, (θ y).toReal)) (y := (z, (θ z).toReal))
    (by simp [← hya]) (by simp [← hzb]) (by linarith : (0 : ℝ) ≤ 1 - s) hs0 (by ring)
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
    Prod.smul_snd, smul_eq_mul] at hmem
  have e : (1 - s) • y + s • z = y + s • (z - y) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rwa [e] at hmem

lemma SAL_incr {m : ℕ} (θ : E m → EReal) (hconv : IsConvexPWLQ θ) (R : PWLQRep m)
    (hrep : IsPWLQRep θ R) {y z : E m} (hy : θ y ≠ ⊤) (hz : θ z ≠ ⊤) :
    ∃ j, y ∈ R.Omega j ∧
      ⟪R.A j y + R.a j, z - y⟫_ℝ ≤ (θ z).toReal - (θ y).toReal := by
  have hbot := hconv.1
  have hcv := hconv.2.1
  set d := z - y with hd
  -- points of the segment are in the domain
  have hseg : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → y + s • d ∈ ⋃ j, R.Omega j := by
    intro s hs0 hs1
    rw [← hrep.2.2.1]
    show θ (y + s • d) < ⊤
    exact lt_of_le_of_lt (SAL_chord θ hbot hcv hy hz hs0 hs1) (EReal.coe_lt_top _)
  have hfreq : ∃ j, ∃ᶠ s in 𝓝[>] (0 : ℝ), y + s • d ∈ R.Omega j := by
    by_contra hcon
    push_neg at hcon
    have h1 := Filter.eventually_all.2 hcon
    have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    obtain ⟨s, hs, hs1, hs0⟩ := (h1.and (h2.and self_mem_nhdsWithin)).exists
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hseg s (le_of_lt hs0) hs1.le)
    exact hs j hj
  obtain ⟨j, hj⟩ := hfreq
  have hcl := SA48_poly_closed (hrep.1 j)
  have hlim : Tendsto (fun s : ℝ => y + s • d) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
    have : Tendsto (fun s : ℝ => y + s • d) (𝓝 0) (𝓝 y) := by
      have hc : Continuous (fun s : ℝ => y + s • d) := by fun_prop
      simpa using hc.tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  have hy0 : y ∈ R.Omega j := hcl.mem_of_frequently_of_tendsto hj hlim
  refine ⟨j, hy0, ?_⟩
  have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨s0, hs0m, hs01, hs00⟩ := (hj.and_eventually (h2.and self_mem_nhdsWithin)).exists
  have hs00' : (0 : ℝ) < s0 := hs00
  have hconvj := SAL_poly_convex (hrep.1 j)
  -- for s ∈ (0, s0], the point is in Ω_j
  have hin : ∀ s, 0 < s → s ≤ s0 → y + s • d ∈ R.Omega j := by
    intro s hs hss
    have := hconvj.add_smul_mem hy0 (y := s0 • d) (by simpa using hs0m)
      (t := s / s0) ⟨by positivity, by rwa [div_le_one hs00']⟩
    rwa [smul_smul, div_mul_cancel₀ s hs00'.ne'] at this
  have hbound : ∀ s, 0 < s → s ≤ s0 →
      ⟪R.A j y + R.a j, d⟫_ℝ + s / 2 * ⟪R.A j d, d⟫_ℝ ≤ (θ z).toReal - (θ y).toReal := by
    intro s hs hss
    have hv := SA48_piece_val θ R hrep j s hy0 (hin s hs hss)
    have hc := SAL_chord θ hbot hcv hy hz hs.le (hss.trans hs01.le)
    rw [hv, EReal.coe_le_coe_iff] at hc
    have : s * (⟪R.A j y + R.a j, d⟫_ℝ + s / 2 * ⟪R.A j d, d⟫_ℝ) ≤
        s * ((θ z).toReal - (θ y).toReal) := by nlinarith
    exact le_of_mul_le_mul_left this hs
  have htend : Tendsto (fun s : ℝ => ⟪R.A j y + R.a j, d⟫_ℝ + s / 2 * ⟪R.A j d, d⟫_ℝ)
      (𝓝[>] (0 : ℝ)) (𝓝 ⟪R.A j y + R.a j, d⟫_ℝ) := by
    have : Tendsto (fun s : ℝ => ⟪R.A j y + R.a j, d⟫_ℝ + s / 2 * ⟪R.A j d, d⟫_ℝ) (𝓝 0)
        (𝓝 ⟪R.A j y + R.a j, d⟫_ℝ) := by
      have hc : Continuous (fun s : ℝ => ⟪R.A j y + R.a j, d⟫_ℝ + s / 2 * ⟪R.A j d, d⟫_ℝ) := by
        fun_prop
      simpa using hc.tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto htend ?_
  have h3 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < s0 :=
    nhdsWithin_le_nhds (gt_mem_nhds hs00')
  filter_upwards [h3, self_mem_nhdsWithin] with s hs1 hs2
  exact hbound s hs2 hs1.le

lemma SAL_lip {m : ℕ} (θ : E m → EReal) (hconv : IsConvexPWLQ θ) (R : PWLQRep m)
    (hrep : IsPWLQRep θ R) (ybar : E m) :
    ∃ ell : ℝ, 0 ≤ ell ∧ ∀ y ∈ Metric.ball ybar 1, θ y ≠ ⊤ →
      ∀ z ∈ Metric.ball ybar 1, θ z ≠ ⊤ →
        |(θ y).toReal - (θ z).toReal| ≤ ell * ‖y - z‖ := by
  set ell : ℝ := ∑ j : Fin R.s, (‖R.A j‖ * (‖ybar‖ + 1) + ‖R.a j‖) with hell
  have hell0 : 0 ≤ ell := Finset.sum_nonneg fun j _ => by positivity
  refine ⟨ell, hell0, ?_⟩
  have key : ∀ y ∈ Metric.ball ybar 1, θ y ≠ ⊤ → ∀ z : E m, θ z ≠ ⊤ →
      -(ell * ‖z - y‖) ≤ (θ z).toReal - (θ y).toReal := by
    intro y hyb hy z hz
    obtain ⟨j, -, hj⟩ := SAL_incr θ hconv R hrep hy hz
    have hyn : ‖y‖ ≤ ‖ybar‖ + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hyb
      have := norm_le_norm_add_norm_sub' y ybar
      linarith [norm_sub_rev y ybar]
    have hg : ‖R.A j y + R.a j‖ ≤ ell := by
      calc ‖R.A j y + R.a j‖ ≤ ‖R.A j y‖ + ‖R.a j‖ := norm_add_le _ _
        _ ≤ ‖R.A j‖ * ‖y‖ + ‖R.a j‖ := by gcongr; exact (R.A j).le_opNorm y
        _ ≤ ‖R.A j‖ * (‖ybar‖ + 1) + ‖R.a j‖ := by gcongr
        _ ≤ ell := Finset.single_le_sum (f := fun j : Fin R.s =>
              ‖R.A j‖ * (‖ybar‖ + 1) + ‖R.a j‖) (fun j _ => by positivity)
              (Finset.mem_univ j)
    have hcs : -(‖R.A j y + R.a j‖ * ‖z - y‖) ≤ ⟪R.A j y + R.a j, z - y⟫_ℝ := by
      have := abs_real_inner_le_norm (R.A j y + R.a j) (z - y)
      have := neg_abs_le ⟪R.A j y + R.a j, z - y⟫_ℝ
      linarith
    have : ‖R.A j y + R.a j‖ * ‖z - y‖ ≤ ell * ‖z - y‖ := by gcongr
    linarith
  intro y hyb hy z hzb hz
  have hn : ‖z - y‖ = ‖y - z‖ := norm_sub_rev z y
  rw [abs_le]
  constructor
  · have := key z hzb hz y hy
    linarith
  · have := key y hyb hy z hz
    rw [hn] at this
    linarith

theorem solution {m : ℕ} (theta : E m → EReal) (hconv : IsConvexPWLQ theta) :
    (∀ y : E m, LowerSemicontinuousAt theta y) ∧
      ∀ ybar ∈ dom theta, ∃ ell : ℝ, LipschitzRelativeAt theta ybar ell := by
  obtain ⟨R, hrep⟩ := hconv.2.2
  have hdomcl : IsClosed (dom theta) := by
    rw [hrep.2.2.1]
    exact isClosed_iUnion_of_finite fun j => SA48_poly_closed (hrep.1 j)
  have hmem : ∀ y, y ∈ dom theta ↔ theta y ≠ ⊤ := fun y =>
    show theta y < ⊤ ↔ theta y ≠ ⊤ from lt_top_iff_ne_top
  refine ⟨fun y => ?_, fun ybar _ => ?_⟩
  · intro c hc
    by_cases hy : y ∈ dom theta
    · have hyr : theta y = ((theta y).toReal : EReal) :=
        (EReal.coe_toReal ((hmem y).1 hy) (hconv.1 y)).symm
      obtain ⟨ell, hell0, hlip⟩ := SAL_lip theta hconv R hrep y
      rw [hyr] at hc
      obtain ⟨c', hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hc
      have hc2' : c' < (theta y).toReal := EReal.coe_lt_coe_iff.1 hc2
      have hδ : 0 < ((theta y).toReal - c') / (ell + 1) := by
        apply div_pos <;> linarith
      filter_upwards [Metric.ball_mem_nhds y (lt_min one_pos hδ)] with z hz
      by_cases hzd : theta z = ⊤
      · rw [hzd]; exact lt_of_lt_of_le hc1 le_top
      · have hzb : z ∈ Metric.ball y 1 := Metric.ball_subset_ball (min_le_left _ _) hz
        have h1 := hlip z hzb hzd y (Metric.mem_ball_self one_pos) ((hmem y).1 hy)
        have hzn : ‖z - y‖ < ((theta y).toReal - c') / (ell + 1) := by
          rw [← dist_eq_norm]; exact lt_of_lt_of_le hz (min_le_right _ _)
        have h2 : ell * ‖z - y‖ ≤ (ell + 1) * ‖z - y‖ := by
          gcongr; linarith
        have h3 : (ell + 1) * ‖z - y‖ < (theta y).toReal - c' := by
          rwa [lt_div_iff₀ (by linarith), mul_comm] at hzn
        have h4 : c' < (theta z).toReal := by
          have := (abs_le.1 h1).1
          linarith
        have hzr : theta z = ((theta z).toReal : EReal) :=
          (EReal.coe_toReal hzd (hconv.1 z)).symm
        rw [hzr]
        exact lt_trans hc1 (EReal.coe_lt_coe_iff.2 h4)
    · filter_upwards [hdomcl.isOpen_compl.mem_nhds hy] with z hz
      have : theta z = ⊤ := by
        by_contra hne; exact hz ((hmem z).2 hne)
      rw [this]
      have : theta y = ⊤ := by
        by_contra hne; exact hy ((hmem y).2 hne)
      rw [this] at hc
      exact hc
  · obtain ⟨ell, hell0, hlip⟩ := SAL_lip theta hconv R hrep ybar
    refine ⟨ell, hell0, Metric.ball ybar 1, Metric.ball_mem_nhds ybar one_pos, ?_⟩
    intro y hy hyd z hz hzd
    exact hlip y hy ((hmem y).1 hyd) z hz ((hmem z).1 hzd)

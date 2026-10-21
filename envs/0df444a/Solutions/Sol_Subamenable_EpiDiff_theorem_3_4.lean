-- Prove2me | solution 1 for Subamenable.EpiDiff.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:55:33.256243+00:00
-- url     : https://prove2.me/submissions/5b8c426e-68b3-4ca7-b40d-1ac86b19c984

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite

set_option autoImplicit false
open Filter Topology Subamenable.EpiDiff
open scoped InnerProductSpace

lemma SA34_mem_dom {k : ℕ} (th : E k → EReal) (z : E k) : z ∈ dom th ↔ th z ≠ ⊤ := by
  show th z < ⊤ ↔ th z ≠ ⊤
  exact lt_top_iff_ne_top

lemma SA34_qval_top (c t : ℝ) (ht : 0 < t) :
    ((⊤ : EReal) - (c : EReal)) * ((t⁻¹ : ℝ) : EReal) = ⊤ := by
  rw [EReal.top_sub_coe]; exact EReal.top_mul_coe_of_pos (inv_pos.2 ht)

lemma SA34_qval_real (A c t : ℝ) :
    ((A : EReal) - (c : EReal)) * ((t⁻¹ : ℝ) : EReal) = (((A - c) * t⁻¹ : ℝ) : EReal) := by
  rw [EReal.coe_mul, EReal.coe_sub]

lemma SA34_g_tendsto {n m : ℕ} (f : E n → E m) (xbar : E n)
    (hdf : DifferentiableAt ℝ f xbar) (w : E n) :
    Tendsto (fun p : ℝ × E n => (p.1, p.1⁻¹ • (f (xbar + p.1 • p.2) - f xbar)))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 (fderiv ℝ f xbar w)) := by
  refine Filter.Tendsto.prodMk tendsto_fst ?_
  set F : Filter (ℝ × E n) := 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w with hF
  have hh : Tendsto (fun p : ℝ × E n => p.1 • p.2) F (𝓝 0) := by
    have h1 : Tendsto (fun p : ℝ × E n => p.1) F (𝓝 0) :=
      (tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝 w)).mono_right nhdsWithin_le_nhds
    have h2 : Tendsto (fun p : ℝ × E n => p.2) F (𝓝 w) := tendsto_snd
    simpa using h1.smul h2
  have hr := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hdf.hasFDerivAt).comp_tendsto hh
  have hbig : (fun p : ℝ × E n => p.1 • p.2) =O[F] (fun p : ℝ × E n => p.1) := by
    refine Asymptotics.IsBigO.of_bound (‖w‖ + 1) ?_
    have h1 : ∀ᶠ y in 𝓝 w, ‖y‖ < ‖w‖ + 1 :=
      (continuous_norm.tendsto w).eventually (gt_mem_nhds (by linarith))
    filter_upwards [tendsto_snd.eventually h1] with p hp
    rw [norm_smul]
    nlinarith [norm_nonneg p.1, norm_nonneg p.2]
  have hr' := hr.trans_isBigO hbig
  have ht := hr'.tendsto_inv_smul_nhds_zero
  have h3 : Tendsto (fun p : ℝ × E n => fderiv ℝ f xbar p.2) F (𝓝 (fderiv ℝ f xbar w)) :=
    ((fderiv ℝ f xbar).continuous.tendsto w).comp tendsto_snd
  have h4 := h3.add ht
  rw [add_zero] at h4
  refine h4.congr' ?_
  have hpos : ∀ᶠ p : ℝ × E n in F, 0 < p.1 :=
    tendsto_fst.eventually (self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0))
  filter_upwards [hpos] with p hp
  simp only [Function.comp]
  have hne : p.1 ≠ 0 := hp.ne'
  have key : p.1⁻¹ • (f (xbar + p.1 • p.2) - f xbar) =
      fderiv ℝ f xbar p.2 +
        p.1⁻¹ • (f (xbar + p.1 • p.2) - f xbar - fderiv ℝ f xbar (p.1 • p.2)) := by
    rw [map_smul, smul_sub, smul_sub, smul_sub, inv_smul_smul₀ hne]; abel
  exact key.symm

lemma SA34_dir1 {n m : ℕ} (theta : E m → EReal) (f : E n → E m) (xbar : E n)
    (hdf : DifferentiableAt ℝ f xbar) (w : E n) :
    subderiv theta (f xbar) (fderiv ℝ f xbar w) ≤
      subderiv (fun x => theta (f x)) xbar w := by
  unfold subderiv
  have h := (SA34_g_tendsto f xbar hdf w).liminf_le_liminf_comp
    (u := fun p : ℝ × E m =>
      (theta (f xbar + p.1 • p.2) - (((theta (f xbar)).toReal : ℝ) : EReal)) *
        ((p.1⁻¹ : ℝ) : EReal))
  refine h.trans (le_of_eq (liminf_congr ?_))
  have hpos : ∀ᶠ p : ℝ × E n in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, 0 < p.1 :=
    tendsto_fst.eventually (self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0))
  filter_upwards [hpos] with p hp
  have hne : p.1 ≠ 0 := hp.ne'
  simp only [Function.comp]
  rw [smul_inv_smul₀ hne, add_sub_cancel]

lemma SA34_key {n m : ℕ} (theta : E m → EReal) (f : E n → E m) (xbar : E n)
    (hdf : DifferentiableAt ℝ f xbar) (hdom : f xbar ∈ dom theta)
    (kappa : ℝ) (hmsqc : MSQC theta f xbar kappa)
    (w : E n) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ → ∀ y : E m, ‖y - fderiv ℝ f xbar w‖ < δ →
      f xbar + t • y ∈ dom theta →
      ∃ w' : E n, ‖w' - w‖ < ε ∧ f (xbar + t • w') ∈ dom theta ∧
        ‖f (xbar + t • w') - (f xbar + t • y)‖ ≤ ε * t := by
  obtain ⟨hk0, U, hU, hUb⟩ := hmsqc
  set D := fderiv ℝ f xbar with hD
  set e : ℝ := min ε 1 with he
  have he0 : 0 < e := lt_min hε one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  set C1 : ℝ := kappa * (‖w‖ + 1) + 1 with hC1
  have hC1pos : 0 < C1 := by
    have : 0 ≤ kappa * (‖w‖ + 1) := mul_nonneg hk0 (by positivity)
    linarith
  set C2 : ℝ := ‖w‖ + 2 + ‖D‖ * C1 with hC2
  have hC2pos : 0 < C2 := by
    have : 0 ≤ ‖D‖ * C1 := mul_nonneg (norm_nonneg _) hC1pos.le
    have := norm_nonneg w
    linarith
  set s : ℝ := min (e / (C1 + 1)) (e / (C2 + 1)) with hs
  have hs0 : 0 < s := lt_min (div_pos he0 (by linarith)) (div_pos he0 (by linarith))
  have hsC1 : s * C1 < e := by
    have : s ≤ e / (C1 + 1) := min_le_left _ _
    rw [le_div_iff₀ (by linarith)] at this
    nlinarith
  have hsC2 : s * C2 ≤ e := by
    have : s ≤ e / (C2 + 1) := min_le_right _ _
    rw [le_div_iff₀ (by linarith)] at this
    nlinarith
  -- local linearization and MSQC neighbourhood
  have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hdf.hasFDerivAt)
  have hlo' := Asymptotics.isLittleO_iff.1 hlo hs0
  obtain ⟨r0, hr0, hr0b⟩ := Metric.eventually_nhds_iff.1 hlo'
  obtain ⟨rU, hrU, hrUb⟩ := Metric.mem_nhds_iff.1 hU
  set r : ℝ := min r0 rU with hr
  have hr_pos : 0 < r := lt_min hr0 hrU
  have hlin : ∀ h : E n, ‖h‖ < r →
      ‖f (xbar + h) - f xbar - D h‖ ≤ s * ‖h‖ ∧ xbar + h ∈ U := by
    intro h hh
    refine ⟨?_, ?_⟩
    · have := hr0b (y := h) (by
        rw [dist_zero_right]; exact lt_of_lt_of_le hh (min_le_left _ _))
      simpa using this
    · apply hrUb
      rw [Metric.mem_ball, dist_eq_norm]
      simpa using lt_of_lt_of_le hh (min_le_right _ _)
  have hw0 := norm_nonneg w
  refine ⟨min s (r / (‖w‖ + 2)), lt_min hs0 (div_pos hr_pos (by linarith)), ?_⟩
  intro t ht0 htδ y hyδ hz
  have hts : t < s := lt_of_lt_of_le htδ (min_le_left _ _)
  have htr : t * (‖w‖ + 2) < r := by
    have := lt_of_lt_of_le htδ (min_le_right _ _)
    rwa [lt_div_iff₀ (by linarith)] at this
  have hys : ‖y - D w‖ < s := lt_of_lt_of_le hyδ (min_le_left _ _)
  -- the point xt
  have htw : ‖t • w‖ < r := by
    rw [norm_smul, Real.norm_of_nonneg ht0.le]; nlinarith
  obtain ⟨hlt, hxtU⟩ := hlin (t • w) htw
  have hz' : ‖f (xbar + t • w) - (f xbar + t • y)‖ ≤ t * s * (‖w‖ + 1) := by
    have e1 : f (xbar + t • w) - (f xbar + t • y) =
        (f (xbar + t • w) - f xbar - D (t • w)) + t • (D w - y) := by
      rw [map_smul, smul_sub]; abel
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖t • (D w - y)‖ ≤ t * s := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le, norm_sub_rev]
      exact mul_le_mul_of_nonneg_left hys.le ht0.le
    have h1 : s * ‖t • w‖ = s * t * ‖w‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le]; ring
    nlinarith
  have hne : (f ⁻¹' dom theta).Nonempty := ⟨xbar, hdom⟩
  have hdist : Metric.infDist (xbar + t • w) (f ⁻¹' dom theta) ≤
      kappa * (t * s * (‖w‖ + 1)) := by
    calc Metric.infDist (xbar + t • w) (f ⁻¹' dom theta)
        ≤ kappa * Metric.infDist (f (xbar + t • w)) (dom theta) := hUb _ hxtU
      _ ≤ kappa * dist (f (xbar + t • w)) (f xbar + t • y) :=
          mul_le_mul_of_nonneg_left (Metric.infDist_le_dist_of_mem hz) hk0
      _ ≤ kappa * (t * s * (‖w‖ + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hk0
          rw [dist_eq_norm]; exact hz'
  have hlt2 : Metric.infDist (xbar + t • w) (f ⁻¹' dom theta) < t * (s * C1) := by
    refine lt_of_le_of_lt hdist ?_
    have h0 : 0 < t * s := mul_pos ht0 hs0
    have e : t * (s * C1) = kappa * (t * s * (‖w‖ + 1)) + t * s := by rw [hC1]; ring
    rw [e]; linarith
  obtain ⟨x', hx'S, hx'd⟩ := (Metric.infDist_lt_iff hne).1 hlt2
  set w' : E n := t⁻¹ • (x' - xbar) with hw'
  have htw' : t • w' = x' - xbar := smul_inv_smul₀ ht0.ne' _
  have hxw' : xbar + t • w' = x' := by rw [htw']; abel
  have hww : ‖w' - w‖ < s * C1 := by
    have e : w' - w = t⁻¹ • (x' - (xbar + t • w)) := by
      rw [hw', show x' - (xbar + t • w) = (x' - xbar) - t • w by abel,
        smul_sub t⁻¹ (x' - xbar) (t • w), inv_smul_smul₀ ht0.ne']
    rw [e, norm_smul, norm_inv, Real.norm_of_nonneg ht0.le, ← dist_eq_norm, dist_comm]
    calc t⁻¹ * dist (xbar + t • w) x' < t⁻¹ * (t * (s * C1)) :=
          mul_lt_mul_of_pos_left hx'd (inv_pos.2 ht0)
      _ = s * C1 := by field_simp
  refine ⟨w', hww.trans (hsC1.trans_le heε), ?_, ?_⟩
  · rw [hxw']; exact hx'S
  · have hw'n : ‖w'‖ ≤ ‖w‖ + 1 := by
      have : ‖w'‖ ≤ ‖w' - w‖ + ‖w‖ := by
        have := norm_sub_norm_le w' w
        linarith [norm_sub_norm_le w' w]
      nlinarith
    have htw'n : ‖t • w'‖ < r := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le]; nlinarith
    obtain ⟨hlt', _⟩ := hlin (t • w') htw'n
    have e1 : f (xbar + t • w') - (f xbar + t • y) =
        (f (xbar + t • w') - f xbar - D (t • w')) + t • (D (w' - w) + (D w - y)) := by
      simp only [map_smul, map_sub, smul_add, smul_sub]; abel
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    have h1 : s * ‖t • w'‖ = s * t * ‖w'‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le]; ring
    have h2 : ‖t • (D (w' - w) + (D w - y))‖ ≤ t * (‖D‖ * (s * C1) + s) := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le]
      apply mul_le_mul_of_nonneg_left _ ht0.le
      refine (norm_add_le _ _).trans ?_
      have h3 : ‖D (w' - w)‖ ≤ ‖D‖ * ‖w' - w‖ := D.le_opNorm _
      have h4 : ‖D w - y‖ ≤ s := by rw [norm_sub_rev]; exact hys.le
      have h5 : ‖D‖ * ‖w' - w‖ ≤ ‖D‖ * (s * C1) :=
        mul_le_mul_of_nonneg_left hww.le (norm_nonneg _)
      linarith
    have h6 : s * t * ‖w'‖ ≤ s * t * (‖w‖ + 1) :=
      mul_le_mul_of_nonneg_left hw'n (by positivity)
    have h7 : t * s * C2 ≤ t * e := by
      have := mul_le_mul_of_nonneg_left hsC2 ht0.le
      linarith
    have h8 : t * e ≤ ε * t := by
      calc t * e = e * t := mul_comm _ _
        _ ≤ ε * t := mul_le_mul_of_nonneg_right heε ht0.le
    have h9 : s * t * (‖w‖ + 1) + t * (‖D‖ * (s * C1) + s) = t * s * C2 := by
      rw [hC2]; ring
    linarith only [hlt', h1, h2, h6, h7, h8, h9]

lemma SA34_dir2 {n m : ℕ} (theta : E m → EReal) (f : E n → E m) (xbar : E n)
    (htheta : ∀ y, theta y ≠ ⊥) (hdom : f xbar ∈ dom theta)
    (hdf : DifferentiableAt ℝ f xbar)
    (ell kappa : ℝ) (hlip : LipschitzRelativeAt theta (f xbar) ell)
    (hmsqc : MSQC theta f xbar kappa) (w : E n) :
    subderiv (fun x => theta (f x)) xbar w ≤ subderiv theta (f xbar) (fderiv ℝ f xbar w) := by
  by_contra hcon
  push_neg at hcon
  set D := fderiv ℝ f xbar with hD
  obtain ⟨a, ha1, ha2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.1 ha2
  have hab : a < b := EReal.coe_lt_coe_iff.1 hb1
  set c : ℝ := (theta (f xbar)).toReal with hc
  have hfreq : ∃ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 (D w),
      (theta (f xbar + p.1 • p.2) - (c : EReal)) * ((p.1⁻¹ : ℝ) : EReal) < (a : EReal) :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) ha1
  have hev : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
      (b : EReal) < (theta (f (xbar + p.1 • p.2)) - (c : EReal)) * ((p.1⁻¹ : ℝ) : EReal) :=
    eventually_lt_of_lt_liminf hb2 (by isBoundedDefault)
  obtain ⟨hell0, UL, hUL, hLip⟩ := hlip
  obtain ⟨rL, hrL, hrLb⟩ := Metric.mem_nhds_iff.1 hUL
  obtain ⟨pa, hpa, pb, hpb, hP⟩ := Filter.eventually_prod_iff.1 hev
  obtain ⟨δ0, hδ0, hδ0b⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hpa)
  obtain ⟨δ1, hδ1, hδ1b⟩ := Metric.eventually_nhds_iff.1 hpb
  set ε : ℝ := min (min 1 ((b - a) / (ell + 1))) δ1 with hε
  have hε0 : 0 < ε :=
    lt_min (lt_min one_pos (div_pos (by linarith) (by linarith))) hδ1
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ (b - a) / (ell + 1) := (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : ε ≤ δ1 := min_le_right _ _
  obtain ⟨δ, hδ, hK⟩ := SA34_key theta f xbar hdf hdom kappa hmsqc w ε hε0
  have hDw := norm_nonneg (D w)
  set δ2 : ℝ := min δ (min δ0 (min (rL / (‖D w‖ + 3)) 1)) with hδ2
  have hδ2pos : 0 < δ2 :=
    lt_min hδ (lt_min hδ0 (lt_min (div_pos hrL (by linarith)) one_pos))
  have hS : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 (D w),
      (0 < p.1 ∧ p.1 < δ2) ∧ ‖p.2 - D w‖ < δ2 := by
    refine Filter.Eventually.prod_mk (pa := fun t => 0 < t ∧ t < δ2)
      (pb := fun y => ‖y - D w‖ < δ2) ?_ ?_
    · exact (show ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t from self_mem_nhdsWithin).and
        ((gt_mem_nhds hδ2pos).filter_mono nhdsWithin_le_nhds)
    · exact Metric.eventually_nhds_iff.2 ⟨δ2, hδ2pos, fun y hy => by simpa [dist_eq_norm] using hy⟩
  obtain ⟨⟨t, y⟩, hQ, ⟨ht0, htδ2⟩, hy⟩ := (hfreq.and_eventually hS).exists
  dsimp only at hQ ht0 htδ2 hy
  have htδ : t < δ := lt_of_lt_of_le htδ2 (min_le_left _ _)
  have htδ0 : t < δ0 :=
    lt_of_lt_of_le htδ2 ((min_le_right _ _).trans (min_le_left _ _))
  have htrL : t < rL / (‖D w‖ + 3) :=
    lt_of_lt_of_le htδ2 ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hy1 : ‖y - D w‖ < 1 :=
    hy.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hyδ : ‖y - D w‖ < δ := hy.trans_le (min_le_left _ _)
  set z := f xbar + t • y with hz
  have hz_ne : theta z ≠ ⊤ := by
    intro h
    rw [h, SA34_qval_top c t ht0] at hQ
    exact absurd hQ (not_lt.2 le_top)
  have hz_real : theta z = ((theta z).toReal : EReal) :=
    (EReal.coe_toReal hz_ne (htheta z)).symm
  rw [hz_real, SA34_qval_real] at hQ
  have hQr : ((theta z).toReal - c) * t⁻¹ < a := EReal.coe_lt_coe_iff.1 hQ
  obtain ⟨w', hw'ε, hw'dom, hw'est⟩ :=
    hK t ht0 htδ y hyδ ((SA34_mem_dom theta z).2 hz_ne)
  have hb' := hP (hδ0b (by rw [Real.dist_eq, sub_zero, abs_of_pos ht0]; exact htδ0) ht0)
    (hδ1b (by rw [dist_eq_norm]; exact lt_of_lt_of_le hw'ε hε3))
  dsimp only at hb'
  have hA_ne : theta (f (xbar + t • w')) ≠ ⊤ := (SA34_mem_dom _ _).1 hw'dom
  have hA_real : theta (f (xbar + t • w')) = ((theta (f (xbar + t • w'))).toReal : EReal) :=
    (EReal.coe_toReal hA_ne (htheta _)).symm
  rw [hA_real, SA34_qval_real] at hb'
  have hb'r : b < ((theta (f (xbar + t • w'))).toReal - c) * t⁻¹ := EReal.coe_lt_coe_iff.1 hb'
  -- Lipschitz estimate
  have hyn : ‖y‖ ≤ ‖D w‖ + 1 := by
    have := norm_sub_norm_le y (D w)
    linarith
  have hzf : ‖z - f xbar‖ ≤ t * (‖D w‖ + 1) := by
    rw [hz, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le]
    exact mul_le_mul_of_nonneg_left hyn ht0.le
  have htrL' : t * (‖D w‖ + 3) < rL := by
    rwa [lt_div_iff₀ (by linarith)] at htrL
  have hzU : z ∈ UL := by
    apply hrLb
    rw [Metric.mem_ball, dist_eq_norm]
    nlinarith
  have hAU : f (xbar + t • w') ∈ UL := by
    apply hrLb
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ‖f (xbar + t • w') - f xbar‖ ≤ ‖f (xbar + t • w') - z‖ + ‖z - f xbar‖ := by
      have := norm_add_le (f (xbar + t • w') - z) (z - f xbar)
      simpa using this
    nlinarith
  have hl := hLip _ hAU ((SA34_mem_dom _ _).2 hA_ne) z hzU ((SA34_mem_dom _ _).2 hz_ne)
  have h1 : (theta (f (xbar + t • w'))).toReal - (theta z).toReal ≤ ell * (ε * t) :=
    (le_abs_self _).trans (hl.trans (mul_le_mul_of_nonneg_left hw'est hell0))
  have h2 : ell * ε ≤ b - a := by
    have : ε * (ell + 1) ≤ b - a := by
      rwa [le_div_iff₀ (by linarith)] at hε2
    nlinarith
  have h3 : ((theta (f (xbar + t • w'))).toReal - (theta z).toReal) * t⁻¹ ≤ ell * ε := by
    calc ((theta (f (xbar + t • w'))).toReal - (theta z).toReal) * t⁻¹
        ≤ (ell * (ε * t)) * t⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 ht0.le)
      _ = ell * ε := by field_simp
  have h4 : ((theta (f (xbar + t • w'))).toReal - c) * t⁻¹ =
      ((theta z).toReal - c) * t⁻¹ +
        ((theta (f (xbar + t • w'))).toReal - (theta z).toReal) * t⁻¹ := by ring
  linarith

theorem solution {n m : ℕ} (theta : E m → EReal) (f : E n → E m)
    (xbar : E n) (htheta : ∀ y, theta y ≠ ⊥) (hdom : f xbar ∈ dom theta)
    (hdf : DifferentiableAt ℝ f xbar)
    (ell kappa : ℝ) (hlip : LipschitzRelativeAt theta (f xbar) ell)
    (hmsqc : MSQC theta f xbar kappa) :
    ∀ w : E n,
      subderiv (fun x => theta (f x)) xbar w =
        subderiv theta (f xbar) (fderiv ℝ f xbar w) := fun w =>
  le_antisymm (SA34_dir2 theta f xbar htheta hdom hdf ell kappa hlip hmsqc w)
    (SA34_dir1 theta f xbar hdf w)

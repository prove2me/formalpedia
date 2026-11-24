-- Prove2me | solution 1 for RoughSurfaceScattering.outwardNormal_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:16:17.935821+00:00
-- url     : https://prove2.me/submissions/b8d50090-3ce7-4d06-b4a5-96caac9e96c9

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory Metric
open RoughSurfaceScattering

/-- The outward unit normal at a boundary point is unique. -/
lemma isOutwardNormal_unique (D : Set R2) (y ν ν' : R2) (h : IsOutwardNormal D y ν)
    (h' : IsOutwardNormal D y ν') : ν = ν' := by
  by_contra hne
  obtain ⟨hn, hc⟩ := h
  obtain ⟨hn', hc'⟩ := h'
  set e := ν' - ν with he
  have he0 : e ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hepos : 0 < ‖e‖ := norm_pos_iff.mpr he0
  set c := @inner ℝ R2 _ ν ν' with hcdef
  have hnn : @inner ℝ R2 _ ν ν = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hnn' : @inner ℝ R2 _ ν' ν' = 1 := by rw [real_inner_self_eq_norm_sq, hn']; norm_num
  have hsym : @inner ℝ R2 _ ν' ν = c := real_inner_comm _ _
  have hesq : ‖e‖ ^ 2 = 2 - 2 * c := by
    rw [← real_inner_self_eq_norm_sq, he, inner_sub_left, inner_sub_right, inner_sub_right,
      hnn, hnn', hsym]; ring
  have hc1 : c < 1 := by nlinarith
  have hen : @inner ℝ R2 _ e ν = c - 1 := by rw [he, inner_sub_left, hsym, hnn]
  have hen' : @inner ℝ R2 _ e ν' = 1 - c := by rw [he, inner_sub_left, hnn', hcdef]
  set ε := (1 - c) / ‖e‖ with hε
  have hεpos : 0 < ε := div_pos (by linarith) hepos
  have hεe : ε * ‖e‖ = 1 - c := div_mul_cancel₀ _ hepos.ne'
  obtain ⟨r1, hr1, h1⟩ := hc ε hεpos
  obtain ⟨r2, hr2, h2⟩ := hc' ε hεpos
  set τ := min r1 r2 / (2 * ‖e‖) with hτ
  have hτpos : 0 < τ := by positivity
  have hτe : τ * ‖e‖ < min r1 r2 := by
    have hm := lt_min hr1 hr2
    rw [hτ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  set z := y + τ • e
  have hzy : z - y = τ • e := by simp [z]
  have hnz : ‖z - y‖ = τ * ‖e‖ := by rw [hzy, norm_smul, Real.norm_of_nonneg hτpos.le]
  have hzne : z ≠ y := by
    intro h; rw [h, sub_self, norm_zero] at hnz
    have := mul_pos hτpos hepos; linarith
  have hz1 : z ∈ ball y r1 := by
    rw [mem_ball, dist_eq_norm, hnz]; exact lt_of_lt_of_le hτe (min_le_left _ _)
  have hz2 : z ∈ ball y r2 := by
    rw [mem_ball, dist_eq_norm, hnz]; exact lt_of_lt_of_le hτe (min_le_right _ _)
  have hin1 : @inner ℝ R2 _ (z - y) ν ≤ -ε * ‖z - y‖ := by
    rw [hnz, hzy, real_inner_smul_left, hen]
    nlinarith
  have hin2 : ε * ‖z - y‖ ≤ @inner ℝ R2 _ (z - y) ν' := by
    rw [hnz, hzy, real_inner_smul_left, hen']
    nlinarith
  exact (h2 z hz2 hzne).2 hin2 ((h1 z hz1 hzne).1 hin1)

lemma abs_coord_le_norm (v : R2) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have h := EuclideanSpace.norm_sq_eq v
  rw [Fin.sum_univ_two] at h
  have h0 : |v i| ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [h, sq_abs]
    fin_cases i
    · simp only [Fin.zero_eta, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 1)]
    · simp only [Fin.mk_one, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 0)]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp h0

/-- The outward normal in a boundary chart `D ∩ B = {(Q(x-p))₂ < g((Q(x-p))₁)}`. -/
noncomputable def chartNormal (Q : R2 ≃ₗᵢ[ℝ] R2) (p : R2) (g : ℝ → ℝ) (y : R2) : R2 :=
  Q.symm ((Real.sqrt (1 + deriv g ((Q (y - p)) 0) ^ 2))⁻¹ • pt (-deriv g ((Q (y - p)) 0)) 1)

lemma continuous_coord (Q : R2 ≃ₗᵢ[ℝ] R2) (p : R2) (i : Fin 2) :
    Continuous fun x : R2 => (Q (x - p)) i :=
  (PiLp.continuous_apply 2 _ i).comp (Q.continuous.comp (continuous_id.sub continuous_const))

lemma continuous_pt1 : Continuous fun a : ℝ => pt (-a) 1 := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

lemma continuous_chartNormal (lam : ℝ) (Q : R2 ≃ₗᵢ[ℝ] R2) (p : R2) (g : ℝ → ℝ)
    (hg : IsC2Lambda lam g) : Continuous (chartNormal Q p g) := by
  have hd : Continuous (deriv g) := hg.1.continuous_deriv (by norm_num)
  have ht : Continuous fun y : R2 => deriv g ((Q (y - p)) 0) := hd.comp (continuous_coord Q p 0)
  have hs : Continuous fun y : R2 => (Real.sqrt (1 + deriv g ((Q (y - p)) 0) ^ 2))⁻¹ :=
    ((ht.pow 2).const_add 1).sqrt.inv₀ fun y =>
      (Real.sqrt_pos.mpr (by simp only [Pi.pow_apply]; positivity)).ne'
  exact Q.symm.continuous.comp (hs.smul (continuous_pt1.comp ht))

lemma norm_pt1 (a : ℝ) : ‖pt (-a) 1‖ = Real.sqrt (1 + a ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [pt, Fin.sum_univ_two]
  ring_nf

/-- A boundary point inside a chart lies on the graph. -/
lemma chart_on_graph (D : Set R2) (hDo : IsOpen D) (p : R2) (Q : R2 ≃ₗᵢ[ℝ] R2) (r : ℝ)
    (g : ℝ → ℝ) (hgc : Continuous g)
    (hch : ∀ x ∈ ball p r, (x ∈ D ↔ (Q (x - p)) 1 < g ((Q (x - p)) 0)))
    (y : R2) (hy : y ∈ frontier D) (hyb : y ∈ ball p r) :
    (Q (y - p)) 1 = g ((Q (y - p)) 0) := by
  have hyD : y ∉ D := by rw [hDo.frontier_eq] at hy; exact hy.2
  have h1 : g ((Q (y - p)) 0) ≤ (Q (y - p)) 1 :=
    not_lt.mp fun h => hyD ((hch y hyb).mpr h)
  refine le_antisymm ?_ h1
  by_contra hlt
  push Not at hlt
  set U := ball p r ∩ {x : R2 | g ((Q (x - p)) 0) < (Q (x - p)) 1}
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_lt (hgc.comp (continuous_coord Q p 0)) (continuous_coord Q p 1))
  obtain ⟨x, hxU, hxD⟩ := mem_closure_iff.mp (frontier_subset_closure hy) U hU ⟨hyb, hlt⟩
  exact lt_asymm hxU.2 ((hch x hxU.1).mp hxD)

/-- The chart normal is an outward unit normal. -/
lemma chart_isOutwardNormal (lam : ℝ) (D : Set R2) (hDo : IsOpen D) (p : R2)
    (Q : R2 ≃ₗᵢ[ℝ] R2) (r : ℝ) (g : ℝ → ℝ) (hg : IsC2Lambda lam g)
    (hch : ∀ x ∈ ball p r, (x ∈ D ↔ (Q (x - p)) 1 < g ((Q (x - p)) 0)))
    (y : R2) (hy : y ∈ frontier D) (hyb : y ∈ ball p r) :
    IsOutwardNormal D y (chartNormal Q p g y) := by
  have hgc : Continuous g := hg.1.continuous
  set t := (Q (y - p)) 0 with ht
  set a := deriv g t with ha
  set s := Real.sqrt (1 + a ^ 2) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  set w : R2 := s⁻¹ • pt (-a) 1 with hw
  have hN : chartNormal Q p g y = Q.symm w := rfl
  have hgt := chart_on_graph D hDo p Q r g hgc hch y hy hyb
  rw [hN]
  refine ⟨?_, fun ε hε => ?_⟩
  · rw [LinearIsometryEquiv.norm_map, hw, norm_smul, norm_pt1, ← hs, norm_inv,
      Real.norm_of_nonneg hspos.le, inv_mul_cancel₀ hspos.ne']
  -- Taylor's bound with tolerance `εs/2`
  have hdiff : DifferentiableAt ℝ g t := hg.1.differentiable (by norm_num) t
  obtain ⟨ρ, hρ, hT⟩ := Metric.eventually_nhds_iff.mp
    (hdiff.hasDerivAt.isLittleO.def (c := ε * s / 2) (by positivity))
  have hyp : dist y p < r := hyb
  refine ⟨min ρ (r - dist y p), lt_min hρ (by linarith), fun z hz hzy => ?_⟩
  have hz' : dist z y < min ρ (r - dist y p) := hz
  have hzr : z ∈ ball p r := by
    have := dist_triangle z y p
    rw [mem_ball]; linarith [min_le_right ρ (r - dist y p)]
  set V := Q (z - y) with hV
  have hVsplit : Q (z - p) = Q (y - p) + V := by
    rw [hV, ← map_add]; congr 1; abel
  have hnV : ‖V‖ = ‖z - y‖ := Q.norm_map _
  have hzpos : 0 < ‖z - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzy)
  have hdu : |V 0| ≤ ‖z - y‖ := hnV ▸ abs_coord_le_norm V 0
  have hinner : @inner ℝ R2 _ (z - y) (Q.symm w) = s⁻¹ * (-a * V 0 + V 1) := by
    rw [← Q.inner_map_eq_flip, ← hV, hw, real_inner_smul_right]
    simp [pt, PiLp.inner_apply, Fin.sum_univ_two]
    try ring
  have hmem : z ∈ D ↔ g t + V 1 < g (t + V 0) := by
    rw [hch z hzr, hVsplit]
    simp only [PiLp.add_apply, ← ht, hgt]
  have hdist : dist (t + V 0) t < ρ := by
    rw [Real.dist_eq, add_sub_cancel_left]
    have := min_le_left ρ (r - dist y p)
    rw [dist_eq_norm] at hz'
    linarith
  have hTay := hT hdist
  simp only [add_sub_cancel_left, Real.norm_eq_abs, smul_eq_mul] at hTay
  have hTl := (abs_le.mp hTay).1
  have hTu := (abs_le.mp hTay).2
  have hsd : ε * s / 2 * |V 0| ≤ ε * s / 2 * ‖z - y‖ :=
    mul_le_mul_of_nonneg_left hdu (by positivity)
  have hεs : 0 < ε * s * ‖z - y‖ := by positivity
  constructor
  · intro h
    rw [hinner] at h
    have h' : V 1 - a * V 0 ≤ -(ε * s * ‖z - y‖) := by
      have := mul_le_mul_of_nonneg_left h hspos.le
      rw [← mul_assoc, mul_inv_cancel₀ hspos.ne', one_mul] at this
      nlinarith
    rw [hmem]
    nlinarith
  · intro h
    rw [hinner] at h
    have h' : ε * s * ‖z - y‖ ≤ V 1 - a * V 0 := by
      have := mul_le_mul_of_nonneg_left h hspos.le
      rw [mul_left_comm, ← mul_assoc s s⁻¹, mul_inv_cancel₀ hspos.ne', one_mul] at this
      nlinarith
    rw [hmem]
    nlinarith

theorem solution (lam : ℝ) (D : Set R2) (hD : IsC2LambdaDomain lam D) :
    ContinuousOn (outwardNormal D) (frontier D) := by
  intro y0 hy0
  obtain ⟨Q, r, g, hr, hg, hch⟩ := hD.2.2.2 y0 hy0
  have heq : ∀ y ∈ frontier D ∩ ball y0 r, outwardNormal D y = chartNormal Q y0 g y := by
    intro y hy
    have hN := chart_isOutwardNormal lam D hD.1 y0 Q r g hg hch y hy.1 hy.2
    have hex : ∃ ν, IsOutwardNormal D y ν := ⟨_, hN⟩
    unfold outwardNormal
    rw [dif_pos hex]
    exact isOutwardNormal_unique D y _ _ hex.choose_spec hN
  have hc := (continuous_chartNormal lam Q y0 g hg).continuousAt (x := y0)
  refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ (heq y0 ⟨hy0, mem_ball_self hr⟩)
  filter_upwards [inter_mem_nhdsWithin (frontier D) (ball_mem_nhds y0 hr)] with y hy
  exact heq y hy

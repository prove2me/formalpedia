-- Prove2me | solution 1 for SpectralProjGrad.SPG1.accumulation_point_stationary
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:07:29.183976+00:00
-- url     : https://prove2.me/submissions/66f81314-25ee-49c5-98f2-b283ca4b7fc3

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_SpectralProjGrad_Shared_IsConstrainedStationary
import Definitions.Def_SpectralProjGrad_Shared_scaledProjGrad
import Definitions.Def_SpectralProjGrad_SPG1_IsSPG1Run

open Filter Topology

namespace SpectralProjGrad.SPG1

open SpectralProjGrad.Shared

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

lemma limit_le {A B C : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → A ≤ B + t * C) : A ≤ B := by
  have ht : Tendsto (fun t : ℝ => B + t * C) (𝓝[>] 0) (𝓝 (B + 0 * C)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
  rw [zero_mul, add_zero] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t htt
  exact h t htt.1 htt.2.le

/-- Variational inequality for the projection onto a convex set. -/
lemma proj_vi {Ω : Set E} {P : E → E} (hΩ : Convex ℝ Ω) (hP : IsProjOnto Ω P) (z y : E)
    (hy : y ∈ Ω) : inner ℝ (z - P z) (y - P z) ≤ 0 := by
  obtain ⟨hPz, hmin⟩ := hP z
  have key : 2 * inner ℝ (z - P z) (y - P z) ≤ 0 := by
    apply limit_le (C := ‖y - P z‖ ^ 2)
    intro t ht0 ht1
    have hmem : P z + t • (y - P z) ∈ Ω := by
      have := hΩ hPz hy (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      convert this using 1; module
    have h := hmin _ hmem
    have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
    have e : z - (P z + t • (y - P z)) = (z - P z) - t • (y - P z) := by abel
    rw [e, norm_sub_sq_real (z - P z) (t • (y - P z)), norm_smul, real_inner_smul_right,
      Real.norm_eq_abs, abs_of_pos ht0] at hsq
    have : t * (2 * inner ℝ (z - P z) (y - P z)) ≤ t * (0 + t * ‖y - P z‖ ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this ht0
  linarith

lemma inner_scaled_le {Ω : Set E} {P : E → E} {f : E → ℝ} (hΩ : Convex ℝ Ω)
    (hP : IsProjOnto Ω P) (t : ℝ) (ht : 0 < t) (x : E) (hx : x ∈ Ω) :
    inner ℝ (gradient f x) (scaledProjGrad P f t x) ≤ -(1 / t) * ‖scaledProjGrad P f t x‖ ^ 2 := by
  have h := proj_vi hΩ hP (x - t • gradient f x) x hx
  set d := scaledProjGrad P f t x with hd
  have e1 : x - t • gradient f x - P (x - t • gradient f x) = -(d + t • gradient f x) := by
    rw [hd, scaledProjGrad]; abel
  have e2 : x - P (x - t • gradient f x) = -d := by rw [hd, scaledProjGrad]; abel
  rw [e1, e2, inner_neg_left, inner_neg_right, neg_neg, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at h
  rw [show -(1 / t) * ‖d‖ ^ 2 = (-‖d‖ ^ 2) / t by ring, le_div_iff₀ ht]
  linarith

lemma scaled_zero_iff {Ω : Set E} {P : E → E} {f : E → ℝ} (hΩ : Convex ℝ Ω)
    (hP : IsProjOnto Ω P) (t : ℝ) (ht : 0 < t) (xbar : E) (hxbar : xbar ∈ Ω) :
    scaledProjGrad P f t xbar = 0 ↔ IsConstrainedStationary Ω f xbar := by
  constructor
  · intro h x hx
    have hP0 : P (xbar - t • gradient f xbar) = xbar := by
      rw [scaledProjGrad, sub_eq_zero] at h; exact h
    have v := proj_vi hΩ hP (xbar - t • gradient f xbar) x hx
    rw [hP0, show xbar - t • gradient f xbar - xbar = -(t • gradient f xbar) by abel,
      inner_neg_left, real_inner_smul_left] at v
    have : 0 ≤ t * inner ℝ (gradient f xbar) (x - xbar) := by linarith
    exact (mul_nonneg_iff_of_pos_left ht).1 this
  · intro hst
    set z := xbar - t • gradient f xbar with hz
    obtain ⟨hPz, hmin⟩ := hP z
    have h1 := hmin xbar hxbar
    have h2 : ‖z - xbar‖ ^ 2 + ‖xbar - P z‖ ^ 2 ≤ ‖z - P z‖ ^ 2 := by
      have e : z - P z = (z - xbar) + (xbar - P z) := by abel
      rw [e, norm_add_sq_real]
      have hzx : z - xbar = -(t • gradient f xbar) := by rw [hz]; abel
      rw [hzx, inner_neg_left, real_inner_smul_left]
      have := hst (P z) hPz
      have e2 : xbar - P z = -(P z - xbar) := by abel
      rw [e2, inner_neg_right]
      nlinarith
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have : ‖xbar - P z‖ ^ 2 ≤ 0 := by linarith
    have hn : ‖xbar - P z‖ = 0 := by nlinarith [norm_nonneg (xbar - P z)]
    rw [norm_eq_zero, sub_eq_zero] at hn
    rw [scaledProjGrad, ← hz, ← hn, sub_self]

/-- Derivative of `f` along a line at a point of differentiability. -/
lemma line_deriv0 (f : E → ℝ) (x d : E) (hfx : DifferentiableAt ℝ f x) :
    HasDerivAt (fun μ : ℝ => f (x + μ • d)) (inner ℝ (gradient f x) d) 0 := by
  have hl : HasDerivAt (fun μ : ℝ => x + μ • d) d 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add x
  have hf : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • d) := by
    rw [zero_smul, add_zero]; exact hfx.hasFDerivAt
  have := hf.comp_hasDerivAt (0:ℝ) hl
  have e : fderiv ℝ f x d = inner ℝ (gradient f x) d := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rw [← e]; exact this


lemma inner_grad_core {Ω : Set E} {P : E → E} {f : E → ℝ} {αmax : ℝ} (hΩ : Convex ℝ Ω)
    (hP : IsProjOnto Ω P) (t : ℝ) (ht : t ∈ Set.Ioc 0 αmax) (x : E) (hx : x ∈ Ω) :
    inner ℝ (gradient f x) (scaledProjGrad P f t x) ≤ -(1 / t) * ‖scaledProjGrad P f t x‖ ^ 2 ∧
      -(1 / t) * ‖scaledProjGrad P f t x‖ ^ 2 ≤ -(1 / αmax) * ‖scaledProjGrad P f t x‖ ^ 2 := by
  refine ⟨inner_scaled_le hΩ hP t ht.1 x hx, ?_⟩
  have h1 : 1 / αmax ≤ 1 / t := one_div_le_one_div_of_le ht.1 ht.2
  have := sq_nonneg ‖scaledProjGrad P f t x‖
  nlinarith

lemma ratio_core {Ω : Set E} {P : E → E} (hΩ : Convex ℝ Ω) (hP : IsProjOnto Ω P)
    (x : E) (hx : x ∈ Ω) (z : E) :
    AntitoneOn (fun s : ℝ => ‖P (x + s • z) - x‖ / s) (Set.Ioi 0) := by
  intro s1 hs1 s2 hs2 hle
  simp only [Set.mem_Ioi] at hs1 hs2
  simp only
  set a := P (x + s1 • z) - x with ha
  set b := P (x + s2 • z) - x with hb
  have v1 := proj_vi hΩ hP (x + s1 • z) (P (x + s2 • z)) (hP _).1
  have v2 := proj_vi hΩ hP (x + s2 • z) (P (x + s1 • z)) (hP _).1
  have e1 : x + s1 • z - P (x + s1 • z) = s1 • z - a := by rw [ha]; abel
  have e2 : P (x + s2 • z) - P (x + s1 • z) = b - a := by rw [ha, hb]; abel
  have e3 : x + s2 • z - P (x + s2 • z) = s2 • z - b := by rw [hb]; abel
  have e4 : P (x + s1 • z) - P (x + s2 • z) = a - b := by rw [ha, hb]; abel
  rw [e1, e2] at v1
  rw [e3, e4] at v2
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left] at v1 v2
  rw [real_inner_self_eq_norm_sq] at v1 v2
  have hab : inner ℝ b a = inner ℝ a b := real_inner_comm _ _
  simp only [hab] at v1 v2
  have cs : inner ℝ a b ≤ ‖a‖ * ‖b‖ := real_inner_le_norm a b
  have key : s2 * ‖a‖ ^ 2 + s1 * ‖b‖ ^ 2 ≤ (s1 + s2) * (‖a‖ * ‖b‖) := by nlinarith
  rw [div_le_div_iff₀ hs2 hs1]
  have hp := norm_nonneg a
  have hq := norm_nonneg b
  by_contra hcon
  push_neg at hcon
  have hprod : (‖a‖ * s2 - ‖b‖ * s1) * (‖a‖ - ‖b‖) ≤ 0 := by nlinarith [key]
  rcases lt_trichotomy ‖a‖ ‖b‖ with hpq | hpq | hpq
  · have : 0 < (‖a‖ * s2 - ‖b‖ * s1) * (‖a‖ - ‖b‖) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    linarith
  · rw [hpq] at hcon; nlinarith
  · nlinarith

lemma P_self {Ω : Set E} {P : E → E} (hP : IsProjOnto Ω P) (x : E) (hx : x ∈ Ω) : P x = x := by
  have h := (hP x).2 x hx
  rw [sub_self, norm_zero] at h
  have : ‖x - P x‖ = 0 := le_antisymm h (norm_nonneg _)
  rw [norm_eq_zero, sub_eq_zero] at this
  exact this.symm

lemma norm_scaled_le {Ω : Set E} {P : E → E} {f : E → ℝ} (hΩ : Convex ℝ Ω)
    (hP : IsProjOnto Ω P) (t : ℝ) (ht : 0 < t) (x : E) (hx : x ∈ Ω) :
    ‖scaledProjGrad P f t x‖ ≤ t * ‖gradient f x‖ := by
  have h := inner_scaled_le (f := f) hΩ hP t ht x hx
  have cs := real_inner_le_norm (gradient f x) (scaledProjGrad P f t x)
  have cs' : -inner ℝ (gradient f x) (scaledProjGrad P f t x) ≤
      ‖gradient f x‖ * ‖scaledProjGrad P f t x‖ := by
    have := abs_real_inner_le_norm (gradient f x) (scaledProjGrad P f t x)
    linarith [neg_abs_le (inner ℝ (gradient f x) (scaledProjGrad P f t x))]
  set d := scaledProjGrad P f t x
  have h2 : ‖d‖ ^ 2 ≤ t * (‖gradient f x‖ * ‖d‖) := by
    have : -(1 / t) * ‖d‖ ^ 2 * t = -‖d‖ ^ 2 := by field_simp
    nlinarith
  rcases eq_or_lt_of_le (norm_nonneg d) with h0 | hpos
  · rw [← h0]; positivity
  · nlinarith

lemma ratio_lower {Ω : Set E} {P : E → E} {f : E → ℝ} (hΩ : Convex ℝ Ω)
    (hP : IsProjOnto Ω P) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (x : E) (hx : x ∈ Ω) :
    t * ‖scaledProjGrad P f 1 x‖ ≤ ‖scaledProjGrad P f t x‖ := by
  have h := ratio_core hΩ hP x hx (-gradient f x) (show t ∈ Set.Ioi (0:ℝ) from ht)
    (show (1:ℝ) ∈ Set.Ioi (0:ℝ) from Set.mem_Ioi.2 one_pos) ht1
  simp only [smul_neg, ← sub_eq_add_neg, div_one, one_smul] at h
  rw [le_div_iff₀ ht] at h
  unfold scaledProjGrad
  rw [one_smul]
  linarith

lemma armijo_core {Ω U : Set E} {f : E → ℝ} {P : E → E} {γ : ℝ}
    (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : IsProjOnto Ω P) (hγ : γ ∈ Set.Ioo 0 1) (x : E) (hx : x ∈ Ω) :
    ∃ sx : ℝ, 0 < sx ∧ ∀ t ∈ Set.Icc 0 sx,
      f (P (x - t • gradient f x)) - f x ≤ γ * inner ℝ (gradient f x) (scaledProjGrad P f t x) := by
  have hPx := P_self hP x hx
  set c := ‖scaledProjGrad P f 1 x‖ with hc
  have t0 : f (P (x - (0:ℝ) • gradient f x)) - f x ≤
      γ * inner ℝ (gradient f x) (scaledProjGrad P f 0 x) := by
    simp [scaledProjGrad, hPx]
  rcases eq_or_lt_of_le (norm_nonneg (scaledProjGrad P f 1 x)) with h0 | hcpos
  · have h0' : scaledProjGrad P f 1 x = 0 := norm_eq_zero.1 h0.symm
    have hst := (scaled_zero_iff hΩ_convex hP 1 one_pos x hx).1 h0'
    refine ⟨1, one_pos, fun t ht => ?_⟩
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h; exact t0
    · have := (scaled_zero_iff hΩ_convex hP t h x hx).2 hst
      rw [this]
      have hP' : P (x - t • gradient f x) = x := by
        rw [scaledProjGrad, sub_eq_zero] at this; exact this
      simp [hP']
  · have hfx : DifferentiableAt ℝ f x :=
      ((hf.differentiableOn (by norm_num)) x (hΩU hx)).differentiableAt (hU_open.mem_nhds (hΩU hx))
    have hlo := hfx.hasFDerivAt.isLittleO
    have hε : 0 < (1 - γ) * c := mul_pos (by linarith [hγ.2]) hcpos
    have hev := hlo.def hε
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set G := ‖gradient f x‖
    refine ⟨min 1 (δ / (G + 1)), lt_min one_pos (by positivity), fun t ht => ?_⟩
    rcases eq_or_lt_of_le ht.1 with h | htpos
    · subst h; exact t0
    have ht1 : t ≤ 1 := ht.2.trans (min_le_left _ _)
    have htδ : t ≤ δ / (G + 1) := ht.2.trans (min_le_right _ _)
    set d := scaledProjGrad P f t x with hd
    have hdn : ‖d‖ ≤ t * G := norm_scaled_le hΩ_convex hP t htpos x hx
    have hG : 0 ≤ G := norm_nonneg _
    have htG : t * G < δ := by
      rw [le_div_iff₀ (by positivity)] at htδ
      nlinarith
    have hy : P (x - t • gradient f x) = x + d := by rw [hd, scaledProjGrad]; abel
    have hb := hball (y := x + d) (by rw [dist_eq_norm, add_sub_cancel_left]; linarith)
    rw [add_sub_cancel_left, Real.norm_eq_abs] at hb
    have e : fderiv ℝ f x d = inner ℝ (gradient f x) d := by
      rw [gradient, InnerProductSpace.toDual_symm_apply]
    rw [e] at hb
    have hb' := (abs_le.1 hb).2
    have hlow := ratio_lower (f := f) hΩ_convex hP t htpos ht1 x hx
    have hin := inner_scaled_le (f := f) hΩ_convex hP t htpos x hx
    rw [← hd] at hlow hin
    have hin2 : inner ℝ (gradient f x) d ≤ -c * ‖d‖ := by
      have h1 : t * inner ℝ (gradient f x) d ≤ -‖d‖ ^ 2 := by
        have : t * (-(1 / t) * ‖d‖ ^ 2) = -‖d‖ ^ 2 := by field_simp
        nlinarith
      have h2 : t * (c * ‖d‖) ≤ ‖d‖ ^ 2 := by nlinarith [norm_nonneg d]
      have : t * inner ℝ (gradient f x) d ≤ t * (-c * ‖d‖) := by nlinarith
      exact le_of_mul_le_mul_left this htpos
    rw [hy]
    nlinarith [hγ.1, hγ.2, norm_nonneg d]

lemma mu_tendsto {σ₁ σ₂ α : ℝ} (hσ₁ : 0 < σ₁) (hσ₂ : σ₂ < 1) (hα : 0 < α) (μ : ℕ → ℝ)
    (hμ0 : μ 0 = α) (hμ : ∀ i, σ₁ * μ i ≤ μ (i + 1) ∧ μ (i + 1) ≤ σ₂ * μ i) :
    (∀ i, 0 < μ i) ∧ Tendsto μ atTop (𝓝 0) := by
  have hμpos : ∀ i, 0 < μ i := by
    intro i; induction i with
    | zero => rw [hμ0]; exact hα
    | succ i ih => exact lt_of_lt_of_le (mul_pos hσ₁ ih) (hμ i).1
  have hσ₂0 : 0 ≤ σ₂ := by
    have := (hμ 0).2; have := hμpos 1; have := hμpos 0; nlinarith
  have hμle : ∀ i, μ i ≤ α * σ₂ ^ i := by
    intro i; induction i with
    | zero => rw [hμ0]; simp
    | succ i ih =>
      calc μ (i + 1) ≤ σ₂ * μ i := (hμ i).2
        _ ≤ σ₂ * (α * σ₂ ^ i) := mul_le_mul_of_nonneg_left ih hσ₂0
        _ = α * σ₂ ^ (i + 1) := by ring
  refine ⟨hμpos, ?_⟩
  have hpow : Tendsto (fun i : ℕ => α * σ₂ ^ i) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hσ₂0 hσ₂).const_mul α
  exact squeeze_zero (fun i => (hμpos i).le) hμle hpow

lemma backtrack_core {Ω U : Set E} {f : E → ℝ} {P : E → E} {γ σ₁ σ₂ α R : ℝ}
    (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : IsProjOnto Ω P) (hγ : γ ∈ Set.Ioo 0 1) (hσ₁ : 0 < σ₁) (hσ₂ : σ₂ < 1)
    (x : E) (hx : x ∈ Ω) (hα : 0 < α) (hR : f x ≤ R)
    (μ : ℕ → ℝ) (hμ0 : μ 0 = α)
    (hμ : ∀ i, σ₁ * μ i ≤ μ (i + 1) ∧ μ (i + 1) ≤ σ₂ * μ i) :
    ∃ i, f (P (x - μ i • gradient f x)) ≤
      R + γ * inner ℝ (P (x - μ i • gradient f x) - x) (gradient f x) := by
  obtain ⟨sx, hsx, hA⟩ := armijo_core hΩ_convex hU_open hΩU hf hP hγ x hx
  obtain ⟨hpos, hlim⟩ := mu_tendsto hσ₁ hσ₂ hα μ hμ0 hμ
  obtain ⟨i, hi⟩ := (hlim.eventually (gt_mem_nhds hsx)).exists
  refine ⟨i, ?_⟩
  have := hA (μ i) ⟨(hpos i).le, hi.le⟩
  rw [scaledProjGrad, real_inner_comm] at this
  linarith

lemma grad_contOn {U : Set E} {f : E → ℝ} (hU_open : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    ContinuousOn (gradient f) U := by
  have h := hf.continuousOn_fderiv_of_isOpen hU_open le_rfl
  have e : gradient f = fun y => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y) := by
    funext y; rfl
  rw [e]
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn h

lemma P_lip {Ω : Set E} {P : E → E} (hΩ : Convex ℝ Ω) (hP : IsProjOnto Ω P) (u v : E) :
    ‖P u - P v‖ ≤ ‖u - v‖ := by
  have h1 := proj_vi hΩ hP u (P v) (hP v).1
  have h2 := proj_vi hΩ hP v (P u) (hP u).1
  have e1 : P v - P u = -(P u - P v) := by abel
  rw [e1, inner_neg_right] at h1
  have h3 : 0 ≤ inner ℝ ((u - P u) - (v - P v)) (P u - P v) := by rw [inner_sub_left]; linarith
  have e2 : (u - P u) - (v - P v) = (u - v) - (P u - P v) := by abel
  rw [e2, inner_sub_left, real_inner_self_eq_norm_sq] at h3
  have cs := real_inner_le_norm (u - v) (P u - P v)
  by_contra hc
  push_neg at hc
  have hA : 0 < ‖P u - P v‖ := lt_of_le_of_lt (norm_nonneg _) hc
  nlinarith

lemma P_cont {Ω : Set E} {P : E → E} (hΩ : Convex ℝ Ω) (hP : IsProjOnto Ω P) : Continuous P := by
  have : LipschitzWith 1 P := LipschitzWith.of_dist_le_mul fun u v => by
    rw [dist_eq_norm, dist_eq_norm]; simpa using P_lip hΩ hP u v
  exact this.continuous

lemma ratio_lower' {Ω : Set E} {P : E → E} {f : E → ℝ} (hΩ : Convex ℝ Ω)
    (hP : IsProjOnto Ω P) (t T : ℝ) (ht : 0 < t) (htT : t ≤ T) (x : E) (hx : x ∈ Ω) :
    t * ‖scaledProjGrad P f T x‖ ≤ T * ‖scaledProjGrad P f t x‖ := by
  have hT : 0 < T := ht.trans_le htT
  have h := ratio_core hΩ hP x hx (-gradient f x) (Set.mem_Ioi.2 ht) (Set.mem_Ioi.2 hT) htT
  simp only [smul_neg, ← sub_eq_add_neg] at h
  rw [div_le_div_iff₀ hT ht] at h
  unfold scaledProjGrad
  linarith

lemma local_core {Ω U : Set E} {f : E → ℝ} {P : E → E} {γ αmax : ℝ}
    (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : IsProjOnto Ω P) (hγ : γ ∈ Set.Ioo 0 1) (hαmax : 0 < αmax) (xbar : E) (hxbar : xbar ∈ Ω)
    (hns : ¬ IsConstrainedStationary Ω f xbar) :
    ∃ ρ > 0, ∃ s > 0, ∃ c > 0, ∀ y ∈ Ω, ‖y - xbar‖ < ρ →
      (∀ t, 0 < t → t ≤ αmax → t * c ≤ ‖scaledProjGrad P f t y‖) ∧
      (∀ t, 0 < t → t ≤ s → t ≤ αmax →
        f (P (y - t • gradient f y)) - f y ≤ γ * inner ℝ (gradient f y) (scaledProjGrad P f t y)) := by
  set φ0 := ‖scaledProjGrad P f αmax xbar‖ with hφ0def
  have hφ0 : 0 < φ0 := by
    rcases eq_or_lt_of_le (norm_nonneg (scaledProjGrad P f αmax xbar)) with h | h
    · exact absurd ((scaled_zero_iff hΩ_convex hP αmax hαmax xbar hxbar).1
        (norm_eq_zero.1 h.symm)) hns
    · exact h
  have hxU : xbar ∈ U := hΩU hxbar
  have hUn : U ∈ 𝓝 xbar := hU_open.mem_nhds hxU
  have hgc : ContinuousAt (gradient f) xbar := (grad_contOn hU_open hf).continuousAt hUn
  have hfdc : ContinuousAt (fderiv ℝ f) xbar :=
    (hf.continuousOn_fderiv_of_isOpen hU_open le_rfl).continuousAt hUn
  have hφc : ContinuousAt (fun y => ‖scaledProjGrad P f αmax y‖) xbar := by
    unfold scaledProjGrad
    apply ContinuousAt.norm
    apply ContinuousAt.sub _ continuousAt_id
    exact (P_cont hΩ_convex hP).continuousAt.comp (continuousAt_id.sub (hgc.const_smul αmax))
  set c := φ0 / (2 * αmax) with hcdef
  have hc : 0 < c := by positivity
  set G0 := ‖gradient f xbar‖ with hG0
  set ε := (1 - γ) * c / 2 with hεdef
  have hε : 0 < ε := by have := hγ.2; rw [hεdef]; nlinarith
  have ev1 : ∀ᶠ y in 𝓝 xbar, φ0 / 2 < ‖scaledProjGrad P f αmax y‖ :=
    hφc.eventually (lt_mem_nhds (by linarith))
  have ev2 : ∀ᶠ y in 𝓝 xbar, ‖gradient f y‖ < G0 + 1 :=
    hgc.norm.eventually (gt_mem_nhds (by linarith))
  have ev3 : ∀ᶠ y in 𝓝 xbar, ‖fderiv ℝ f y - fderiv ℝ f xbar‖ < ε / 2 := by
    have := hfdc.eventually (Metric.ball_mem_nhds (fderiv ℝ f xbar) (half_pos hε))
    simpa [Metric.mem_ball, dist_eq_norm] using this
  have ev4 : ∀ᶠ y in 𝓝 xbar, y ∈ U := hUn
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.eventually_nhds_iff_ball.1 (ev1.and (ev2.and (ev3.and ev4)))
  refine ⟨ρ0 / 2, half_pos hρ0, ρ0 / (2 * (G0 + 1)), by positivity, c, hc, ?_⟩
  intro y hy hyρ
  have hyb : y ∈ Metric.ball xbar ρ0 := by rw [Metric.mem_ball, dist_eq_norm]; linarith
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hball y hyb
  have part1 : ∀ t, 0 < t → t ≤ αmax → t * c ≤ ‖scaledProjGrad P f t y‖ := by
    intro t ht htT
    have h := ratio_lower' (f := f) hΩ_convex hP t αmax ht htT y hy
    have e : t * c = (t * (φ0 / 2)) / αmax := by rw [hcdef]; field_simp
    rw [e, div_le_iff₀ hαmax]
    nlinarith
  refine ⟨part1, ?_⟩
  intro t ht hts htT
  set d := scaledProjGrad P f t y with hd
  have hdn : ‖d‖ ≤ t * ‖gradient f y‖ := norm_scaled_le hΩ_convex hP t ht y hy
  have hdn2 : ‖d‖ ≤ ρ0 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hts
    have : t * ‖gradient f y‖ ≤ t * (G0 + 1) := mul_le_mul_of_nonneg_left hy2.le ht.le
    nlinarith
  have hyd : y + d ∈ Metric.ball xbar ρ0 := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖y + d - xbar‖ = ‖(y - xbar) + d‖ := by congr 1; abel
      _ ≤ ‖y - xbar‖ + ‖d‖ := norm_add_le _ _
      _ < ρ0 := by linarith
  have hderiv : ∀ w ∈ Metric.ball xbar ρ0,
      HasFDerivWithinAt f (fderiv ℝ f w) (Metric.ball xbar ρ0) w := fun w hw =>
    (((hf.differentiableOn (by norm_num)) w (hball w hw).2.2.2).differentiableAt
      (hU_open.mem_nhds (hball w hw).2.2.2)).hasFDerivAt.hasFDerivWithinAt
  have hbound : ∀ w ∈ Metric.ball xbar ρ0, ‖fderiv ℝ f w - fderiv ℝ f y‖ ≤ ε := by
    intro w hw
    have a1 := (hball w hw).2.2.1
    calc ‖fderiv ℝ f w - fderiv ℝ f y‖
        = ‖(fderiv ℝ f w - fderiv ℝ f xbar) - (fderiv ℝ f y - fderiv ℝ f xbar)‖ := by
          congr 1; abel
      _ ≤ ‖fderiv ℝ f w - fderiv ℝ f xbar‖ + ‖fderiv ℝ f y - fderiv ℝ f xbar‖ := norm_sub_le _ _
      _ ≤ ε := by linarith
  have hmvt := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' hderiv hbound
    (convex_ball xbar ρ0) hyb hyd
  rw [add_sub_cancel_left] at hmvt
  have e : fderiv ℝ f y d = inner ℝ (gradient f y) d := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rw [e, Real.norm_eq_abs] at hmvt
  have hm := (abs_le.1 hmvt).2
  have hin := inner_scaled_le (f := f) hΩ_convex hP t ht y hy
  rw [← hd] at hin
  have hlow := part1 t ht htT
  rw [← hd] at hlow
  have hin2 : inner ℝ (gradient f y) d ≤ -c * ‖d‖ := by
    have h1 : t * inner ℝ (gradient f y) d ≤ -‖d‖ ^ 2 := by
      have : t * (-(1 / t) * ‖d‖ ^ 2) = -‖d‖ ^ 2 := by field_simp
      nlinarith
    have h2 : t * (c * ‖d‖) ≤ ‖d‖ ^ 2 := by nlinarith [norm_nonneg d]
    have : t * inner ℝ (gradient f y) d ≤ t * (-c * ‖d‖) := by nlinarith
    exact le_of_mul_le_mul_left this ht
  have hy' : P (y - t • gradient f y) = y + d := by rw [hd, scaledProjGrad]; abel
  rw [hy']
  have hγ1 := hγ.2
  have hnd := norm_nonneg d
  have : ε * ‖d‖ ≤ -(1 - γ) * inner ℝ (gradient f y) d := by
    rw [hεdef]; nlinarith
  nlinarith

lemma ref_ge' (f : E → ℝ) (x : ℕ → E) (M k j : ℕ) (hj : j ≤ min k (M - 1)) :
    f (x (k - j)) ≤ nonmonotoneRef f x M k := by
  unfold nonmonotoneRef
  exact Finset.le_sup' (fun j => f (x (k - j))) (Finset.mem_range.2 (by omega))

lemma ref_ge (f : E → ℝ) (x : ℕ → E) (M k : ℕ) : f (x k) ≤ nonmonotoneRef f x M k := by
  simpa using ref_ge' f x M k 0 (Nat.zero_le _)

lemma ref_succ {f : E → ℝ} {x : ℕ → E} {M k : ℕ} (h : f (x (k + 1)) ≤ nonmonotoneRef f x M k) :
    nonmonotoneRef f x M (k + 1) ≤ nonmonotoneRef f x M k := by
  conv_lhs => unfold nonmonotoneRef
  apply Finset.sup'_le
  intro j hj
  rw [Finset.mem_range] at hj
  rcases j with _ | j
  · simpa using h
  · have := ref_ge' f x M k j (by omega)
    show f (x (k + 1 - (j + 1))) ≤ _
    rw [show k + 1 - (j + 1) = k - j by omega]
    exact this

lemma ref_window {f : E → ℝ} {x : ℕ → E} {M : ℕ} (hM : 1 ≤ M) (k : ℕ) :
    ∃ i ≤ M - 1, nonmonotoneRef f x M (k + M) = f (x (k + 1 + i)) := by
  unfold nonmonotoneRef
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_range_add_one (n := min (k + M) (M - 1)))
    (fun j => f (x (k + M - j)))
  rw [Finset.mem_range] at hj
  refine ⟨M - 1 - j, by omega, he.trans ?_⟩
  show f (x (k + M - j)) = _
  rw [show k + M - j = k + 1 + (M - 1 - j) by omega]

lemma seq_core {Ω : Set E} {f : E → ℝ} {G : E → E} {M : ℕ} {γ αmax : ℝ}
    (hΩ_closed : IsClosed Ω) (hfc : ContinuousOn f Ω) (hGc : ContinuousOn G Ω)
    (xbar : E) (hfx : ContinuousAt f xbar)
    (hM : 1 ≤ M) (hγ : 0 < γ) (hαmax : 0 < αmax)
    (x : ℕ → E) (δ : ℕ → ℝ) (hxΩ : ∀ k, x k ∈ Ω)
    (hstep : ∀ k, ‖x (k + 1) - x k‖ ≤ αmax * ‖G (x k)‖)
    (hdδ : ∀ k, ‖x (k + 1) - x k‖ ^ 2 ≤ αmax * δ k)
    (hδ0 : ∀ k, 0 ≤ δ k)
    (htest : ∀ k, f (x (k + 1)) ≤ nonmonotoneRef f x M k - γ * δ k)
    (hclu : MapClusterPt xbar atTop x) :
    ∀ η > 0, ∃ N, ∀ k ≥ N, ‖x k - xbar‖ ≤ 1 → δ k ≤ η := by
  set W := nonmonotoneRef f x M with hWdef
  have hW1 : ∀ k, f (x k) ≤ W k := fun k => ref_ge f x M k
  have hWs : ∀ k, f (x (k + 1)) ≤ W k := fun k => by
    linarith [htest k, mul_nonneg hγ.le (hδ0 k)]
  have hanti : Antitone W := antitone_nat_of_succ_le (fun k => ref_succ (hWs k))
  have hbdd : BddBelow (Set.range W) := by
    have ev : ∀ᶠ y in 𝓝 xbar, f xbar - 1 < f y := hfx.eventually (lt_mem_nhds (by linarith))
    refine ⟨f xbar - 1, ?_⟩
    rintro _ ⟨k, rfl⟩
    obtain ⟨j, hj, hj2⟩ := (Filter.frequently_atTop.1 (hclu.frequently ev)) k
    linarith [hanti hj, hW1 j]
  set L := ⨅ k, W k with hLdef
  have hLW : ∀ k, L ≤ W k := fun k => ciInf_le hbdd k
  have hWL : ∀ η > 0, ∃ N, ∀ k ≥ N, W k ≤ L + η := by
    intro η hη
    obtain ⟨N, hN⟩ := exists_lt_of_ciInf_lt (show L < L + η by linarith)
    exact ⟨N, fun k hk => (hanti hk).trans hN.le⟩
  have hwin : ∀ k, ∃ i ≤ M - 1, W (k + M) = f (x (k + 1 + i)) := fun k => ref_window hM k
  have fwd : ∀ N, ∃ r, ∀ k, ‖x k - xbar‖ ≤ 1 → ∀ i ≤ N, ‖x (k + i) - xbar‖ ≤ r := by
    intro N
    induction N with
    | zero => exact ⟨1, fun k hk i hi => by rw [Nat.le_zero.1 hi, add_zero]; exact hk⟩
    | succ N ih =>
      obtain ⟨r, hr⟩ := ih
      obtain ⟨C, hC⟩ := ((isCompact_closedBall xbar r).inter_right hΩ_closed).exists_bound_of_continuousOn
        (hGc.mono Set.inter_subset_right)
      refine ⟨r + αmax * max C 0, fun k hk i hi => ?_⟩
      have hpos : 0 ≤ αmax * max C 0 := mul_nonneg hαmax.le (le_max_right _ _)
      rcases Nat.lt_or_ge i (N + 1) with h | h
      · linarith [hr k hk i (by omega)]
      · have hi' : i = N + 1 := by omega
        subst hi'
        have h1 := hr k hk N le_rfl
        have h2 := hstep (k + N)
        have h3 := hC (x (k + N)) ⟨by rw [Metric.mem_closedBall, dist_eq_norm]; exact h1, hxΩ _⟩
        have h4 : αmax * ‖G (x (k + N))‖ ≤ αmax * max C 0 :=
          mul_le_mul_of_nonneg_left (h3.trans (le_max_left _ _)) hαmax.le
        have e : x (k + (N + 1)) - xbar = (x (k + N + 1) - x (k + N)) + (x (k + N) - xbar) := by
          rw [← add_assoc]; abel
        rw [e]
        have := norm_add_le (x (k + N + 1) - x (k + N)) (x (k + N) - xbar)
        linarith
  obtain ⟨r, hr⟩ := fwd M
  set K := Metric.closedBall xbar r ∩ Ω with hKdef
  have hK : IsCompact K := (isCompact_closedBall xbar r).inter_right hΩ_closed
  have huc := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous (hfc.mono Set.inter_subset_right))
  have memK : ∀ k, ‖x k - xbar‖ ≤ 1 → ∀ i ≤ M, x (k + i) ∈ K := fun k hk i hi =>
    ⟨by rw [Metric.mem_closedBall, dist_eq_norm]; exact hr k hk i hi, hxΩ _⟩
  have Q : ∀ s, s ≤ M - 1 → ∀ η > 0, ∃ N, ∀ k ≥ N, ‖x k - xbar‖ ≤ 1 →
      ∃ j ≤ M - 1 - s, L - η ≤ f (x (k + 1 + j)) := by
    intro s
    induction s with
    | zero =>
      intro _ η hη
      refine ⟨0, fun k _ _ => ?_⟩
      obtain ⟨i, hi, he⟩ := hwin k
      exact ⟨i, by omega, by rw [← he]; linarith [hLW (k + M)]⟩
    | succ s ih =>
      intro hs η hη
      obtain ⟨ρ, hρ, hρu⟩ := huc (η / 2) (half_pos hη)
      set η' := min (η / 2) (γ * ρ ^ 2 / (4 * αmax)) with hη'
      have hη'pos : 0 < η' := lt_min (half_pos hη) (by positivity)
      have hη'1 : η' ≤ η / 2 := min_le_left _ _
      have hη'2 : η' ≤ γ * ρ ^ 2 / (4 * αmax) := min_le_right _ _
      obtain ⟨N1, hN1⟩ := ih (by omega) η' hη'pos
      obtain ⟨N2, hN2⟩ := hWL η' hη'pos
      refine ⟨max N1 N2, fun k hk hxk => ?_⟩
      have hk1 : N1 ≤ k := le_of_max_le_left hk
      have hk2 : N2 ≤ k := le_of_max_le_right hk
      obtain ⟨j, hj, hfj⟩ := hN1 k hk1 hxk
      by_cases hjs : j ≤ M - 1 - (s + 1)
      · exact ⟨j, hjs, by linarith⟩
      · set i := M - 1 - (s + 1) with hi
        have hji : k + 1 + j = (k + 1 + i) + 1 := by omega
        rw [hji] at hfj
        have hW := hN2 (k + 1 + i) (by omega)
        have ht := htest (k + 1 + i)
        have hδs : γ * δ (k + 1 + i) ≤ 2 * η' := by linarith
        have hd2 := hdδ (k + 1 + i)
        have h4 : η' * (4 * αmax) ≤ γ * ρ ^ 2 := (le_div_iff₀ (by positivity)).1 hη'2
        have hsq : ‖x (k + 1 + i + 1) - x (k + 1 + i)‖ ^ 2 < ρ ^ 2 := by
          have h5 : γ * (αmax * δ (k + 1 + i)) ≤ γ * (ρ ^ 2 / 2) := by nlinarith
          have h6 : αmax * δ (k + 1 + i) ≤ ρ ^ 2 / 2 := le_of_mul_le_mul_left h5 hγ
          nlinarith
        have hsmall : ‖x (k + 1 + i + 1) - x (k + 1 + i)‖ < ρ := by
          by_contra hcon
          push_neg at hcon
          have := pow_le_pow_left₀ hρ.le hcon 2
          linarith
        have hkK1 : x (k + 1 + i) ∈ K := by
          have := memK k hxk (1 + i) (by omega)
          rwa [← add_assoc] at this
        have hkK2 : x (k + 1 + i + 1) ∈ K := by
          have := memK k hxk (1 + i + 1) (by omega)
          rwa [show k + (1 + i + 1) = k + 1 + i + 1 by ring] at this
        have hc := hρu _ hkK2 _ hkK1 (by rw [dist_eq_norm]; exact hsmall)
        rw [Real.dist_eq] at hc
        refine ⟨i, le_rfl, ?_⟩
        have := (abs_lt.1 hc)
        linarith
  intro η hη
  obtain ⟨N1, hN1⟩ := Q (M - 1) le_rfl (γ * η / 2) (by positivity)
  obtain ⟨N2, hN2⟩ := hWL (γ * η / 2) (by positivity)
  refine ⟨max N1 N2, fun k hk hxk => ?_⟩
  obtain ⟨j, hj, hfj⟩ := hN1 k (le_of_max_le_left hk) hxk
  have hj0 : j = 0 := by omega
  subst hj0
  have h1 := hN2 k (le_of_max_le_right hk)
  have h2 := htest k
  simp only [add_zero] at hfj
  have : γ * δ k ≤ γ * η := by linarith
  exact le_of_mul_le_mul_left this hγ

lemma spectral_mem (αmin αmax : ℝ) (h : αmin < αmax) (s y : E) :
    spectralStep αmin αmax s y ∈ Set.Icc αmin αmax := by
  unfold spectralStep
  split_ifs
  · exact ⟨h.le, le_rfl⟩
  · exact ⟨le_min h.le (le_max_left _ _), min_le_left _ _⟩

theorem goal_core {Ω U : Set E} {f : E → ℝ} {P : E → E}
    {M : ℕ} {αmin αmax γ σ₁ σ₂ : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : IsProjOnto Ω P)
    (hM : 1 ≤ M) (hαmin : 0 < αmin) (hαmin_lt : αmin < αmax)
    (hγ : γ ∈ Set.Ioo 0 1) (hσ₁ : 0 < σ₁) (hσ₂ : σ₂ < 1)
    {x : ℕ → E} {α : ℕ → ℝ}
    (hrun : IsSPG1Run Ω f P M αmin αmax γ σ₁ σ₂ x α)
    (xbar : E) (hxbar : MapClusterPt xbar atTop x) :
    IsConstrainedStationary Ω f xbar := by
  have hαmax : 0 < αmax := hαmin.trans hαmin_lt
  have hαk : ∀ k, α k ∈ Set.Icc αmin αmax := by
    intro k; cases k with
    | zero => exact hrun.start_step
    | succ k => rw [hrun.step3_spectral k]; exact spectral_mem αmin αmax hαmin_lt _ _
  choose m μ hμ0 hμ hfail htest hnext using hrun.step2_backtrack
  have hμpos : ∀ k, ∀ i ≤ m k, 0 < μ k i ∧ μ k i ≤ α k := by
    intro k i hi
    induction i with
    | zero => rw [hμ0]; exact ⟨hαmin.trans_le (hαk k).1, le_rfl⟩
    | succ i ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      have a := hμ k i (by omega)
      exact ⟨lt_of_lt_of_le (mul_pos hσ₁ h1) a.1, by nlinarith [a.2]⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : ℕ → ℝ, lam = fun k => μ k (m k) := ⟨_, rfl⟩
  have hlamk : ∀ k, lam k = μ k (m k) := fun k => by rw [hlam]
  have hlam1 : ∀ k, 0 < lam k ∧ lam k ≤ αmax := fun k => by
    rw [hlamk]; exact ⟨(hμpos k _ le_rfl).1, (hμpos k _ le_rfl).2.trans (hαk k).2⟩
  have hxΩ : ∀ k, x k ∈ Ω := by
    intro k; cases k with
    | zero => exact hrun.start_mem
    | succ k => rw [hnext k]; exact (hP _).1
  have hd : ∀ k, x (k + 1) - x k = scaledProjGrad P f (lam k) (x k) := fun k => by
    rw [hnext k, hlamk]; rfl
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℕ → ℝ, δ = fun k => -inner ℝ (gradient f (x k)) (x (k + 1) - x k) :=
    ⟨_, rfl⟩
  have hδk : ∀ k, δ k = -inner ℝ (gradient f (x k)) (x (k + 1) - x k) := fun k => by rw [hδdef]
  have hin : ∀ k, inner ℝ (gradient f (x k)) (x (k + 1) - x k) ≤
      -(1 / lam k) * ‖x (k + 1) - x k‖ ^ 2 := fun k => by
    rw [hd k]; exact inner_scaled_le hΩ_convex hP _ (hlam1 k).1 _ (hxΩ k)
  have hlδ : ∀ k, ‖x (k + 1) - x k‖ ^ 2 ≤ lam k * δ k := by
    intro k
    have h := hin k
    have hl := (hlam1 k).1
    have : lam k * (-(1 / lam k) * ‖x (k + 1) - x k‖ ^ 2) = -‖x (k + 1) - x k‖ ^ 2 := by
      field_simp
    rw [hδk]; nlinarith
  have hδ0 : ∀ k, 0 ≤ δ k := fun k => by
    have := (sq_nonneg _).trans (hlδ k)
    exact le_of_mul_le_mul_left (by rw [mul_zero]; exact this) (hlam1 k).1
  have hdδ : ∀ k, ‖x (k + 1) - x k‖ ^ 2 ≤ αmax * δ k := fun k =>
    (hlδ k).trans (mul_le_mul_of_nonneg_right (hlam1 k).2 (hδ0 k))
  have hstep : ∀ k, ‖x (k + 1) - x k‖ ≤ αmax * ‖gradient f (x k)‖ := fun k => by
    rw [hd k]
    exact (norm_scaled_le hΩ_convex hP _ (hlam1 k).1 _ (hxΩ k)).trans
      (mul_le_mul_of_nonneg_right (hlam1 k).2 (norm_nonneg _))
  have htest' : ∀ k, f (x (k + 1)) ≤ nonmonotoneRef f x M k - γ * δ k := by
    intro k
    have h := htest k
    unfold SPG1Test at h
    rw [← hnext k, real_inner_comm] at h
    rw [hδk]; linarith
  have hxbarΩ : xbar ∈ Ω := by
    by_contra h
    obtain ⟨k, hk⟩ := (hxbar.frequently (hΩ_closed.isOpen_compl.mem_nhds h)).exists
    exact hk (hxΩ k)
  have hfxbar : ContinuousAt f xbar :=
    (((hf.differentiableOn (by norm_num)) xbar (hΩU hxbarΩ)).differentiableAt
      (hU_open.mem_nhds (hΩU hxbarΩ))).continuousAt
  have hA := seq_core hΩ_closed (hf.continuousOn.mono hΩU) ((grad_contOn hU_open hf).mono hΩU)
    xbar hfxbar hM hγ.1 hαmax x δ hxΩ hstep hdδ hδ0 htest' hxbar
  by_contra hns
  obtain ⟨ρ, hρ, s, hs, c, hc, hB⟩ :=
    local_core hΩ_convex hU_open hΩU hf hP hγ hαmax xbar hxbarΩ hns
  set τ := min αmin (σ₁ * min s αmax) with hτdef
  have hτ : 0 < τ := lt_min hαmin (mul_pos hσ₁ (lt_min hs hαmax))
  have hlamlow : ∀ k, ‖x k - xbar‖ < ρ → τ ≤ lam k := by
    intro k hk
    by_contra hlt
    push_neg at hlt
    have hlt1 : lam k < αmin := lt_of_lt_of_le hlt (min_le_left _ _)
    have hlt2 : lam k < σ₁ * min s αmax := lt_of_lt_of_le hlt (min_le_right _ _)
    rcases Nat.eq_zero_or_pos (m k) with h0 | hpos
    · rw [hlamk, h0, hμ0] at hlt1
      linarith [(hαk k).1]
    · obtain ⟨p, hp⟩ : ∃ p, m k = p + 1 := ⟨m k - 1, by omega⟩
      have hf1 := hfail k p (by omega)
      have hμp := hμpos k p (by omega)
      have hstepp := hμ k p (by omega)
      have hlk : lam k = μ k (p + 1) := by rw [hlamk, hp]
      have ht' : μ k p < min s αmax := by
        have : σ₁ * μ k p < σ₁ * min s αmax := by linarith [hstepp.1]
        exact lt_of_mul_lt_mul_left this hσ₁.le
      have hArm := (hB (x k) (hxΩ k) hk).2 (μ k p) hμp.1 (ht'.le.trans (min_le_left _ _))
        (ht'.le.trans (min_le_right _ _))
      apply hf1
      unfold SPG1Test
      rw [scaledProjGrad, real_inner_comm] at hArm
      have := ref_ge f x M k
      linarith
  have hδlow : ∀ k, ‖x k - xbar‖ < ρ → τ * c ^ 2 ≤ δ k := by
    intro k hk
    have h1 := (hB (x k) (hxΩ k) hk).1 (lam k) (hlam1 k).1 (hlam1 k).2
    rw [← hd k] at h1
    have h2 := hlδ k
    have h3 := hlamlow k hk
    have hl := (hlam1 k).1
    have h4 : (lam k * c) ^ 2 ≤ lam k * δ k := (pow_le_pow_left₀ (by positivity) h1 2).trans h2
    have h5 : lam k * c ^ 2 ≤ δ k := by
      have : lam k * (lam k * c ^ 2) ≤ lam k * δ k := by nlinarith
      exact le_of_mul_le_mul_left this hl
    nlinarith [sq_nonneg c]
  obtain ⟨N, hN⟩ := hA (τ * c ^ 2 / 2) (by positivity)
  obtain ⟨k, hkN, hk⟩ := Filter.frequently_atTop.1
    (hxbar.frequently (p := fun y => y ∈ Metric.ball xbar (min ρ 1))
      (Metric.ball_mem_nhds xbar (lt_min hρ one_pos))) N
  simp only [Metric.mem_ball, dist_eq_norm] at hk
  have h1 := hN k hkN (hk.le.trans (min_le_right _ _))
  have h2 := hδlow k (hk.trans_le (min_le_left _ _))
  have : 0 < τ * c ^ 2 := by positivity
  linarith

end SpectralProjGrad.SPG1

open SpectralProjGrad.SPG1


theorem solution {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {M : ℕ} {αmin αmax γ σ₁ σ₂ : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hM : 1 ≤ M) (hαmin : 0 < αmin) (hαmin_lt : αmin < αmax)
    (hγ : γ ∈ Set.Ioo 0 1) (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) (hσ₂ : σ₂ < 1)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {α : ℕ → ℝ}
    (hrun : IsSPG1Run Ω f P M αmin αmax γ σ₁ σ₂ x α)
    (xbar : EuclideanSpace ℝ (Fin n)) (hxbar : MapClusterPt xbar Filter.atTop x) :
    SpectralProjGrad.Shared.IsConstrainedStationary Ω f xbar := by
  exact goal_core hΩ_closed hΩ_convex hU_open hΩU hf hP hM hαmin hαmin_lt hγ hσ₁ hσ₂ hrun xbar hxbar

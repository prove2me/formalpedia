-- Prove2me | solution 1 for SpectralProjGrad.SPG1.armijo_along_projection_arc
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:00:40.401387+00:00
-- url     : https://prove2.me/submissions/85591dc2-d58f-4f47-9ca1-70f95019a01d

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

end SpectralProjGrad.SPG1

open SpectralProjGrad.SPG1


theorem solution {n : ℕ}
    {Ω U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {γ : ℝ}
    (hΩ_closed : IsClosed Ω) (hΩ_convex : Convex ℝ Ω)
    (hU_open : IsOpen U) (hΩU : Ω ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hP : SpectralProjGrad.Shared.IsProjOnto Ω P)
    (hγ : γ ∈ Set.Ioo 0 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) :
    ∃ sx : ℝ, 0 < sx ∧ ∀ t ∈ Set.Icc 0 sx,
      f (P (x - t • gradient f x)) - f x ≤ γ * inner ℝ (gradient f x) (SpectralProjGrad.Shared.scaledProjGrad P f t x) := by
  exact armijo_core hΩ_convex hU_open hΩU hf hP hγ x hx

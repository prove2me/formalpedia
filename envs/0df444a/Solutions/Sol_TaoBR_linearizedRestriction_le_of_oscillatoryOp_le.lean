-- Prove2me | solution 1 for TaoBR.linearizedRestriction_le_of_oscillatoryOp_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T13:49:44.99519+00:00
-- url     : https://prove2.me/submissions/28051d99-8a3e-48c0-9cab-a9e0cfdbea66

import Mathlib
import Definitions.Def_TaoBR
import Theorems.Thm_TaoBR_exists_sparse_cover
import Theorems.Thm_TaoBR_linearizedMeasure_fourier_decay_of_oscillatoryOp_le

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
/-!
# Blueprint: Theorem 4.9 (Tao, p. 10) as a reduction to the Fourier-decay leaf

Target (published, frozen): `TaoBR.linearizedRestriction_le_of_oscillatoryOp_le`.
Only Open import: `TaoBR.linearizedMeasure_fourier_decay_of_oscillatoryOp_le` (the leaf: under
the hypotheses of Theorem 4.9, for real `1 ≤ q`, `q < p`, the measure
`μ_q = (∇_y φ(·, y₀))_* (|ψ(·, y₀)|^q dx)` has power Fourier decay).

Write `Φ(x) = ∇_y φ(x, y₀)` (`Grad φ y₀`), `μ_q = muQ φ ψ y₀ q`. The conclusion for `q` is
`‖f̂‖_{L^q(μ_q)} ≲ ‖f‖_q`.

Route.
1. **Linearization** (`local_estimate_of_oscillatoryOp_le`): `hS` gives, for every `ε > 0`, the
   localized estimate `‖ψ(·, y₀) ĝ(Φ(·))‖_{Lᵖ(dx)} ≲ L^ε ‖g‖_p` for bounded measurable `g`
   supported in `B(0, L)`. Test `S_R` on `f(y) = g(R(y - y₀))` with `R = L^{m+2}`; the phase error
   `R φ(x, y₀ + z/R) - R φ(x, y₀) - ⟨Φ(x), z⟩ = O(L²/R)` and `ψ(x, y₀ + z/R) - ψ(x, y₀) = O(L/R)`
   are absorbed pointwise using `|ĝ| ≤ ‖g‖₁ ≲ L^{m}‖g‖_p`.
2. **Weights** (`restrMu_muQ_of_local`): the weight in step 1 is `|ψ|^p`, the leaf's is `|ψ|^q`.
   Interpolate (real interpolation, `interp_L1_Lp`) the step-1 bound on each dyadic level set
   `{|ψ| ≈ M 2^{-k}}` with the trivial `L¹ → L¹` bound `|ĝ| ≤ ‖g‖₁`, and sum over `k`: for
   `q < r < 1 + q/p'` the series converges and gives `R_{μ_q}(r, α)` for every `α > 0`.
3. **Generic ε-removal without Frostman** (`top_L2w`, `smoothed_of_restrMu`, `sparse_of_restrMu`,
   `restrMu_zero_of_cubeUnion_bound`, `restrMu_zero_of_restrMu`): the parab Blueprint's chain
   (`proofs/parab`, Parts A–D) with the thickened set estimate replaced by the smoothed measure
   `Wt μ R = |K_R| * μ`: the diagonal `L²` and the `L¹` bounds are taken in `L²(Wt)`, `L¹(Wt)`
   (no Frostman), the input `∫ |ĝ|^p Wt ≲ R^{αp} ‖g‖_p^p` is the average of `R_μ(p, α)` over
   modulations, and a floor `R^{-n}` added to the weight absorbs the off-diagonal terms.
4. **Normalization** (`exists_scale_decayMeasure`, `restrMu_scale_of_restrMu`,
   `restrMu_of_restrMu_scale`): `μ_q` pushed by `ξ ↦ ξ / λ` lies in `B(0, 3/2)` and decays (leaf).
5. **Back to the conclusion** (`conclusion_of_restrMu`): cutoff approximation of a Schwartz `f`.
6. **Degenerate cases**: `m = 0`; `p = ∞` and `p > 2` (then `ψ(·, y₀) = 0`, by testing step 1 on
   modulated bumps); `m = 1` (rank `0`: `Φ` is locally constant where `ψ(·, y₀) ≠ 0`, so a bump
   at scale `L` concentrated at that value violates step 1); `ψ(·, y₀) ≡ 0` is trivial.

Every lemma below except the target is a `sorry` stub; the target is proved from them.
-/
/-! ## Generic objects (verbatim from the parab Blueprint) -/
/-- The Fourier transform of a measure, `μ̂(x) = ∫ e(-⟪ξ, x⟫) dμ(ξ)`. -/
noncomputable def ftMeasure {n : ℕ} (μ : Measure (E n)) (x : E n) : ℂ :=
  ∫ ξ, (𝐞 (-⟪ξ, x⟫) : ℂ) ∂μ

/-- `R_μ(p, α)`: `‖f̂‖_{Lᵖ(μ)} ≲ R^α ‖f‖_p` for Schwartz `f` supported in `B(0, R)`, `R ≥ 1`. -/
def RestrMu {n : ℕ} (μ : Measure (E n)) (p α : ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ closedBall 0 R →
    eLpNorm (𝓕 (f : E n → ℂ)) (ENNReal.ofReal p) μ ≤
      C * ENNReal.ofReal (R ^ α) * eLpNorm f (ENNReal.ofReal p) volume

/-- The bump of Lemma 3.2 (`rIn = 1/32`, `rOut = 1/16`). -/
noncomputable def bump (n : ℕ) : ContDiffBump (0 : E n) := ⟨1 / 32, 1 / 16, by norm_num, by norm_num⟩

/-- `Φ ≥ 0`, `∫ Φ = 1`, supported in `B(0, 1/16)`. -/
noncomputable def Phi (n : ℕ) (v : E n) : ℝ := (bump n).normed volume v

/-- The kernel `K(v) = R^n Φ(R v) e(-⟪v, c⟫)`. -/
noncomputable def Kker (n : ℕ) (R : ℝ) (c v : E n) : ℂ :=
  ((R ^ n : ℝ) : ℂ) * (Phi n (R • v) : ℂ) * (𝐞 (-⟪v, c⟫) : ℂ)

/-- The operator `T G (ω) = Σ_i ∫ K_i(ω - η) G_i(η) dη` of Lemma 3.2. -/
noncomputable def Top {n N : ℕ} (R : ℝ) (x : Fin N → E n) (G : Fin N → E n → ℂ) (ω : E n) : ℂ :=
  ∑ i, ∫ η, Kker n R (x i) (ω - η) * G i η

/-! ## New generic objects -/
/-- A finite measure carried by `S ⊆ B(0, 3/2)` with power Fourier decay (the parab Blueprint's
`GoodMeasure` without the Frostman bound). -/
structure DecayMeasure {n : ℕ} (μ : Measure (E n)) (S : Set (E n)) : Prop where
  finite : IsFiniteMeasure μ
  null_compl : μ Sᶜ = 0
  subset : S ⊆ closedBall 0 (3 / 2)
  decay : ∃ C c : ℝ, 0 < c ∧ ∀ x : E n, ‖ftMeasure μ x‖ ≤ C * (1 + ‖x‖) ^ (-c)

/-- The smoothed measure `Wt μ R (η) = ∫ |K_R(ω - η)| dμ(ω) = (R^n Φ(R ·) * μ)(η)`. -/
noncomputable def Wt {n : ℕ} (μ : Measure (E n)) (R : ℝ) (η : E n) : ℝ≥0∞ :=
  ∫⁻ ω, ‖Kker n R 0 (ω - η)‖ₑ ∂μ

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise
namespace TaoBR.Tao49.PartW1
/-!
# Part W1 of the Theorem 4.9 Blueprint: `top_L2w` (port of `proofs/parab/PartA.lean`)

The Frostman cap bound is replaced by the smoothed weight `Wt μ R`; the off-diagonal terms are
bounded by `Cst R^{-n}/N` (separation exponent `3nm + 3n + 3`) and absorbed by the floor `R^{-n}`.
-/
/-! ## The bump `Φ` and `φ = 𝓕⁻ Φ` -/
noncomputable abbrev PhiC (n : ℕ) (v : E n) : ℂ := (Phi n v : ℂ)

noncomputable def MPhi (n : ℕ) : ℝ := 1 / (volume : Measure (E n)).real (closedBall 0 (1 / 32))

lemma Phi_nonneg (n : ℕ) (v : E n) : 0 ≤ Phi n v := (bump n).nonneg_normed v

lemma Phi_le (n : ℕ) (v : E n) : Phi n v ≤ MPhi n :=
  (bump n).normed_le_div_measure_closedBall_rIn volume v

lemma Phi_support (n : ℕ) {v : E n} (h : Phi n v ≠ 0) : ‖v‖ < 1 / 16 := by
  have : v ∈ Function.support ((bump n).normed volume) := h
  rw [(bump n).support_normed_eq, mem_ball_zero_iff] at this
  exact this

lemma Phi_integral (n : ℕ) : ∫ v, Phi n v = 1 := (bump n).integral_normed

lemma PhiC_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (PhiC n) :=
  Complex.ofRealCLM.contDiff.comp (bump n).contDiff_normed

lemma PhiC_hasCompactSupport (n : ℕ) : HasCompactSupport (PhiC n) :=
  (bump n).hasCompactSupport_normed.comp_left Complex.ofReal_zero

noncomputable def PhiS (n : ℕ) : 𝓢(E n, ℂ) :=
  (PhiC_hasCompactSupport n).toSchwartzMap (PhiC_contDiff n)

/-- `φ = 𝓕⁻ Φ` as a Schwartz map. -/
noncomputable def phiS (n : ℕ) : 𝓢(E n, ℂ) := 𝓕⁻ (PhiS n)

noncomputable def phi (n : ℕ) : E n → ℂ := phiS n

lemma phi_eq (n : ℕ) (y : E n) : phi n y = ∫ v, (𝐞 ⟪v, y⟫ : ℂ) * PhiC n v := by
  rw [phi, phiS, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  rfl

lemma phi_integrable (n : ℕ) : Integrable (phi n) := (phiS n).integrable

lemma phi_moment_integrable (n : ℕ) : Integrable (fun u : E n => ‖u‖ * ‖phi n u‖) := by
  simpa [phi] using (phiS n).integrable_pow_mul volume 1

lemma phi_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (phi n) := (phiS n).smooth ⊤

lemma Phi_integrable (n : ℕ) : Integrable (Phi n) := (bump n).integrable_normed

/-- `φ_c(x) = φ((x - c)/R)`. -/
noncomputable def phiLoc (n : ℕ) (R : ℝ) (c : E n) (x : E n) : ℂ := phi n (R⁻¹ • (x - c))

end TaoBR.Tao49.PartW1
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise
namespace TaoBR.Tao49.PartW1
variable {n : ℕ} {R : ℝ} {c : E n}
lemma K_support (hR : 0 < R) {v : E n} (h : Kker n R c v ≠ 0) : ‖v‖ < 1 / (16 * R) := by
  have h1 : PhiC n (R • v) ≠ 0 := by
    intro h0; apply h; simp only [Kker, h0, mul_zero, zero_mul]
  have h2 : Phi n (R • v) ≠ 0 := by simpa [PhiC] using h1
  have h3 := Phi_support n h2
  rw [norm_smul, Real.norm_of_nonneg hR.le] at h3
  rw [lt_div_iff₀ (by positivity)]; linarith

lemma K_norm_le (hR : 0 < R) (v : E n) : ‖Kker n R c v‖ ≤ R ^ n * MPhi n := by
  simp only [Kker, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Phi_nonneg n _)]
  exact mul_le_mul_of_nonneg_left (Phi_le n _) (by positivity)

lemma K_continuous : Continuous (Kker n R c) := by
  have h1 : Continuous (PhiC n) := (PhiC_contDiff n).continuous
  have h2 : Continuous (fun v : E n => (𝐞 (-⟪v, c⟫) : ℂ)) :=
    (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const).neg).subtype_val
  have h3 : Continuous (fun v : E n => PhiC n (R • v)) := h1.comp (continuous_const_smul R)
  exact (continuous_const.mul h3).mul h2

lemma K_integrable (hR : 0 < R) : Integrable (Kker n R c) := by
  refine K_continuous.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E n) (1 / (16 * R))) (fun v hv => ?_)
  by_contra h
  exact hv (mem_closedBall_zero_iff.2 (K_support hR h).le)

lemma fourierInv_K (hR : 0 < R) : 𝓕⁻ (Kker n R c) = phiLoc n R c := by
  funext y
  rw [Real.fourierInv_eq, phiLoc, phi_eq]
  have hcv := MeasureTheory.Measure.integral_comp_smul (volume : Measure (E n))
    (fun u : E n => (𝐞 ⟪u, R⁻¹ • (y - c)⟫ : ℂ) * PhiC n u) R
  rw [finrank_euclideanSpace_fin] at hcv
  have e1 : ∀ v : E n, 𝐞 ⟪v, y⟫ • Kker n R c v =
      ((R ^ n : ℝ) : ℂ) * ((𝐞 ⟪R • v, R⁻¹ • (y - c)⟫ : ℂ) * PhiC n (R • v)) := by
    intro v
    rw [Circle.smul_def, Kker, smul_eq_mul]
    have : ⟪R • v, R⁻¹ • (y - c)⟫ = ⟪v, y⟫ + -⟪v, c⟫ := by
      rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hR.ne',
        one_mul, inner_sub_right]; ring
    rw [this, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  simp_rw [e1]
  rw [integral_const_mul, hcv, Complex.real_smul, abs_of_pos (by positivity)]
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (by positivity),
    Complex.ofReal_one, one_mul]

lemma phiLoc_integrable (hR : 0 < R) : Integrable (phiLoc n R c) := by
  have h1 : Integrable (fun y : E n => phi n (R⁻¹ • y)) :=
    (phi_integrable n).comp_smul (inv_ne_zero hR.ne')
  have h2 := h1.comp_sub_right c
  exact h2

lemma fourier_phiLoc (hR : 0 < R) : 𝓕 (phiLoc n R c) = Kker n R c := by
  have hF : 𝓕 (Kker n R c) = fun w => phiLoc n R c (-w) := by
    funext w
    rw [← fourierInv_K hR, Real.fourierInv_eq_fourier_neg, neg_neg]
  have hFi : Integrable (𝓕 (Kker n R c)) := by
    rw [hF]
    have := (phiLoc_integrable (c := c) hR).comp_smul (show (-1 : ℝ) ≠ 0 by norm_num)
    simpa using this
  rw [← fourierInv_K hR]
  exact K_continuous.fourier_fourierInv_eq (K_integrable hR) hFi

lemma phiLoc_contDiff : ContDiff ℝ (⊤ : ℕ∞) (phiLoc n R c) := by
  exact (phi_contDiff n).comp (by fun_prop)

lemma phiLoc_L1 (hR : 0 < R) : ∫ x, ‖phiLoc n R c x‖ = R ^ n * ∫ u, ‖phi n u‖ := by
  have h1 := integral_sub_right_eq_self (fun y : E n => ‖phi n (R⁻¹ • y)‖) (μ := volume) c
  have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (E n))
    (fun y : E n => ‖phi n y‖) hR.le
  rw [finrank_euclideanSpace_fin] at h2
  simp only [phiLoc]
  rw [h1, h2, smul_eq_mul]

lemma phiLoc_moment_integrable (hR : 0 < R) :
    Integrable (fun x => ‖x - c‖ * ‖phiLoc n R c x‖) := by
  have h0 : Integrable (fun u : E n => R * (‖u‖ * ‖phi n u‖)) :=
    (phi_moment_integrable n).const_mul R
  have h1 : Integrable (fun y : E n => R * (‖R⁻¹ • y‖ * ‖phi n (R⁻¹ • y)‖)) :=
    h0.comp_smul (inv_ne_zero hR.ne')
  have h2 := h1.comp_sub_right c
  refine h2.congr (Eventually.of_forall (fun y => ?_))
  simp only [phiLoc, norm_smul, norm_inv, Real.norm_of_nonneg hR.le]
  field_simp

lemma phiLoc_moment (hR : 0 < R) :
    ∫ x, ‖x - c‖ * ‖phiLoc n R c x‖ = R ^ (n + 1) * ∫ u, ‖u‖ * ‖phi n u‖ := by
  have h1 := integral_sub_right_eq_self
    (fun y : E n => ‖y‖ * ‖phi n (R⁻¹ • y)‖) (μ := volume) c
  have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (E n))
    (fun u : E n => R * (‖u‖ * ‖phi n u‖)) hR.le
  rw [finrank_euclideanSpace_fin] at h2
  have e : ∀ y : E n, R * (‖R⁻¹ • y‖ * ‖phi n (R⁻¹ • y)‖) = ‖y‖ * ‖phi n (R⁻¹ • y)‖ := by
    intro y
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hR.le]; field_simp
  simp_rw [e] at h2
  simp only [phiLoc]
  rw [h1, h2, smul_eq_mul, integral_const_mul]; ring

/-- Weighted Cauchy–Schwarz for lower integrals. -/
lemma lintegral_cs {α : Type*} [MeasurableSpace α] (μ : Measure α) {a b : α → ℝ≥0∞}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) :
    (∫⁻ t, a t * b t ∂μ) ^ 2 ≤ (∫⁻ t, a t ∂μ) * ∫⁻ t, a t * b t ^ 2 ∂μ := by
  have hf : AEMeasurable (fun t => a t ^ (1 / 2 : ℝ)) μ := ha.pow_const _
  have hg : AEMeasurable (fun t => a t ^ (1 / 2 : ℝ) * b t) μ := hf.mul hb
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have e1 : ∀ t, a t ^ (1 / 2 : ℝ) * (a t ^ (1 / 2 : ℝ) * b t) = a t * b t := by
    intro t
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ t, (a t ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a t := by
    intro t; rw [← ENNReal.rpow_mul]; norm_num
  have e3 : ∀ t, (a t ^ (1 / 2 : ℝ) * b t) ^ (2 : ℝ) = a t * b t ^ 2 := by
    intro t; rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2, ← ENNReal.rpow_natCast]
    norm_num
  simp only [Pi.mul_apply, e1, e2, e3] at h
  calc (∫⁻ t, a t * b t ∂μ) ^ 2
      ≤ ((∫⁻ t, a t ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ t, a t * b t ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = (∫⁻ t, a t ∂μ) * ∫⁻ t, a t * b t ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

end TaoBR.Tao49.PartW1
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise
namespace TaoBR.Tao49.PartW1
variable {n : ℕ} {R : ℝ} {c : E n}
variable {n : ℕ} {R : ℝ} {μ : Measure (E n)} [IsFiniteMeasure μ]
lemma K_lintegral (hR : 0 < R) (c : E n) : ∫⁻ v, ‖Kker n R c v‖ₑ = 1 := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (K_integrable hR)]
  have e : ∀ v : E n, ‖Kker n R c v‖ = R ^ n * Phi n (R • v) := by
    intro v
    simp only [Kker, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one]
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Phi_nonneg n _)]
  simp_rw [e]
  rw [integral_const_mul, Measure.integral_comp_smul, finrank_euclideanSpace_fin, Phi_integral,
    smul_eq_mul, mul_one, abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity),
    ENNReal.ofReal_one]

/-- `F(ω) = ∫ K(ω - η) G(η) dη`. -/
noncomputable def Fop (n : ℕ) (R : ℝ) (c : E n) (G : E n → ℂ) (ω : E n) : ℂ :=
  ∫ η, Kker n R c (ω - η) * G η

/-- `g(y) = ∫ e(⟪y, η⟫) G(η) dη`. -/
noncomputable def gG (G : E n → ℂ) (y : E n) : ℂ := ∫ η, (𝐞 ⟪y, η⟫ : ℂ) * G η

lemma gG_enorm_le (G : E n → ℂ) (y : E n) : ‖gG G y‖ₑ ≤ ∫⁻ η, ‖G η‖ₑ := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1; ext η
  rw [enorm_mul, ← ofReal_norm (𝐞 ⟪y, η⟫ : ℂ), Circle.norm_coe, ENNReal.ofReal_one, one_mul]

lemma gG_norm_le (G : E n → ℂ) (y : E n) : ‖gG G y‖ ≤ ∫ η, ‖G η‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext η; rw [norm_mul, Circle.norm_coe, one_mul]

lemma gG_meas {G : E n → ℂ} (hG : StronglyMeasurable G) : StronglyMeasurable (gG G) := by
  refine StronglyMeasurable.integral_prod_right (f := fun (y η : E n) => (𝐞 ⟪y, η⟫ : ℂ) * G η) ?_
  refine StronglyMeasurable.mul ?_ (hG.comp_measurable measurable_snd)
  exact (Real.continuous_fourierChar.comp (continuous_fst.inner continuous_snd)).subtype_val
    |>.stronglyMeasurable

lemma sig_meas : StronglyMeasurable (ftMeasure μ) := by
  refine StronglyMeasurable.integral_prod_left'
    (f := fun p : E n × E n => (𝐞 (-⟪p.1, p.2⟫) : ℂ)) ?_
  exact (Real.continuous_fourierChar.comp ((continuous_fst).inner
    continuous_snd).neg).subtype_val.stronglyMeasurable

lemma sig_norm_le (z : E n) : ‖ftMeasure μ z‖ ≤ μ.real univ := by
  have := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun ω : E n => (𝐞 (-⟪ω, z⟫) : ℂ)) (C := 1)
    (Eventually.of_forall (fun ω => (Circle.norm_coe _).le))
  simpa [ftMeasure] using this

lemma conj_e (t : ℝ) : conj (𝐞 t : ℂ) = (𝐞 (-t) : ℂ) := by
  rw [← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv]

lemma Fop_repr (hR : 0 < R) (c : E n) {G : E n → ℂ} (hG : Integrable G) (ω : E n) :
    Fop n R c G ω = ∫ y, phiLoc n R c y * gG G y * (𝐞 (-⟪y, ω⟫) : ℂ) := by
  have hK : ∀ v, Kker n R c v = ∫ y, (𝐞 (-⟪y, v⟫) : ℂ) * phiLoc n R c y := by
    intro v; rw [← fourier_phiLoc hR, Real.fourier_eq]; rfl
  have e1 : ∀ η, Kker n R c (ω - η) * G η =
      ∫ y, phiLoc n R c y * ((𝐞 ⟪y, η⟫ : ℂ) * G η) * (𝐞 (-⟪y, ω⟫) : ℂ) := by
    intro η
    rw [hK, ← integral_mul_const]
    congr 1; ext y
    have : -⟪y, ω - η⟫ = ⟪y, η⟫ + -⟪y, ω⟫ := by rw [inner_sub_right]; ring
    rw [this, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  unfold Fop
  simp_rw [e1]
  have hint : Integrable (Function.uncurry fun (η y : E n) =>
      phiLoc n R c y * ((𝐞 ⟪y, η⟫ : ℂ) * G η) * (𝐞 (-⟪y, ω⟫) : ℂ)) (volume.prod volume) := by
    have hp : Integrable (fun p : E n × E n => G p.1 * phiLoc n R c p.2) (volume.prod volume) :=
      hG.mul_prod (phiLoc_integrable hR)
    refine hp.mono ?_ (Eventually.of_forall (fun p => ?_))
    · refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ (AEStronglyMeasurable.mul ?_
        hG.aestronglyMeasurable.comp_fst)) ?_
      · exact (phiLoc_contDiff.continuous.comp continuous_snd).aestronglyMeasurable
      · exact (Real.continuous_fourierChar.comp (continuous_snd.inner continuous_fst)).subtype_val
          |>.aestronglyMeasurable
      · exact (Real.continuous_fourierChar.comp (continuous_snd.inner
          continuous_const).neg).subtype_val.aestronglyMeasurable
    · simp [Function.uncurry, Circle.norm_coe, mul_comm]
  rw [integral_integral_swap hint]
  congr 1; ext y
  rw [integral_mul_const, integral_const_mul]; rfl

lemma Fop_offdiag (hR : 0 < R) (c c' : E n) {G G' : E n → ℂ} (hG : Integrable G)
    (hG' : Integrable G') (hGm : StronglyMeasurable G) (hGm' : StronglyMeasurable G') :
    ‖∫ ω, Fop n R c G ω * conj (Fop n R c' G' ω) ∂(μ)‖ₑ ≤
      (∫⁻ η, ‖G η‖ₑ) * (∫⁻ η, ‖G' η‖ₑ) *
        ∫⁻ y, ∫⁻ y', ‖phiLoc n R c y‖ₑ * ‖phiLoc n R c' y'‖ₑ * ‖ftMeasure μ (y - y')‖ₑ := by
  set h : E n → ℂ := fun y => phiLoc n R c y * gG G y with hh_def
  set h' : E n → ℂ := fun y => phiLoc n R c' y * gG G' y with hh'_def
  have hhm : StronglyMeasurable h :=
    phiLoc_contDiff.continuous.stronglyMeasurable.mul (gG_meas hGm)
  have hhm' : StronglyMeasurable h' :=
    phiLoc_contDiff.continuous.stronglyMeasurable.mul (gG_meas hGm')
  have hh : Integrable h :=
    (phiLoc_integrable hR).mul_bdd (gG_meas hGm).aestronglyMeasurable
      (Eventually.of_forall (fun y => gG_norm_le G y))
  have hh' : Integrable h' :=
    (phiLoc_integrable hR).mul_bdd (gG_meas hGm').aestronglyMeasurable
      (Eventually.of_forall (fun y => gG_norm_le G' y))
  have hF : ∀ ω : E n, Fop n R c G ω = ∫ y, h y * (𝐞 (-⟪y, ω⟫) : ℂ) :=
    fun ω => Fop_repr hR c hG ω
  have hF' : ∀ ω : E n, Fop n R c' G' ω = ∫ y, h' y * (𝐞 (-⟪y, ω⟫) : ℂ) :=
    fun ω => Fop_repr hR c' hG' ω
  have hprod : ∀ ω : E n, Fop n R c G ω * conj (Fop n R c' G' ω) =
      ∫ p : E n × E n, h p.1 * conj (h' p.2) * (𝐞 (-⟪ω, p.1 - p.2⟫) : ℂ) := by
    intro ω
    rw [hF, hF', ← integral_conj, ← integral_prod_mul]
    congr 1; ext p
    rw [map_mul, conj_e, inner_sub_right, real_inner_comm ω p.1, real_inner_comm ω p.2]
    have : -(⟪ω, p.1⟫ - ⟪ω, p.2⟫) = -⟪ω, p.1⟫ + -(-⟪ω, p.2⟫) := by ring
    rw [this, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  simp_rw [hprod]
  have hint : Integrable (Function.uncurry fun (ω : E n) (p : E n × E n) =>
      h p.1 * conj (h' p.2) * (𝐞 (-⟪ω, p.1 - p.2⟫) : ℂ))
      ((μ).prod volume) := by
    have h1 : Integrable (fun p : E n × E n => ‖h p.1‖ * ‖h' p.2‖) volume :=
      hh.norm.mul_prod hh'.norm
    have h2 : Integrable (fun q : E n × (E n × E n) =>
        (1 : ℝ) * (‖h q.2.1‖ * ‖h' q.2.2‖)) ((μ).prod volume) :=
      (integrable_const (1 : ℝ)).mul_prod h1
    refine h2.mono ?_ (Eventually.of_forall (fun q => ?_))
    · refine StronglyMeasurable.aestronglyMeasurable ?_
      refine StronglyMeasurable.mul (StronglyMeasurable.mul ?_ ?_) ?_
      · exact hhm.comp_measurable (measurable_fst.comp measurable_snd)
      · exact (Complex.continuous_conj.comp_stronglyMeasurable
          (hhm'.comp_measurable (measurable_snd.comp measurable_snd)))
      · exact (Real.continuous_fourierChar.comp ((continuous_fst).inner ((continuous_fst.comp continuous_snd).sub
          (continuous_snd.comp continuous_snd))).neg).subtype_val.stronglyMeasurable
    · simp [Function.uncurry, Circle.norm_coe]
  rw [integral_integral_swap hint]
  have hsig : ∀ p : E n × E n, ∫ ω : E n,
      h p.1 * conj (h' p.2) * (𝐞 (-⟪ω, p.1 - p.2⟫) : ℂ) ∂(μ) =
      h p.1 * conj (h' p.2) * ftMeasure μ (p.1 - p.2) := by
    intro p; rw [integral_const_mul]; rfl
  simp_rw [hsig]
  set A := ∫⁻ η, ‖G η‖ₑ
  set A' := ∫⁻ η, ‖G' η‖ₑ
  have hA : A ≠ ⊤ := hG.2.ne
  have hA' : A' ≠ ⊤ := hG'.2.ne
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hmeas : AEMeasurable (fun p : E n × E n =>
      ‖phiLoc n R c p.1‖ₑ * ‖phiLoc n R c' p.2‖ₑ * ‖ftMeasure μ (p.1 - p.2)‖ₑ) volume := by
    refine Measurable.aemeasurable ?_
    have m1 : Measurable (fun p : E n × E n => ‖phiLoc n R c p.1‖ₑ) :=
      ((phiLoc_contDiff (c := c) (R := R)).continuous.comp continuous_fst).measurable.enorm
    have m2 : Measurable (fun p : E n × E n => ‖phiLoc n R c' p.2‖ₑ) :=
      ((phiLoc_contDiff (c := c') (R := R)).continuous.comp continuous_snd).measurable.enorm
    have m3 : Measurable (fun p : E n × E n => ‖ftMeasure μ (p.1 - p.2)‖ₑ) :=
      ((sig_meas (n := n)).measurable.comp (measurable_fst.sub measurable_snd)).enorm
    exact (m1.mul m2).mul m3
  calc ∫⁻ p : E n × E n, ‖h p.1 * conj (h' p.2) * ftMeasure μ (p.1 - p.2)‖ₑ
      ≤ ∫⁻ p : E n × E n, A * A' * (‖phiLoc n R c p.1‖ₑ * ‖phiLoc n R c' p.2‖ₑ * ‖ftMeasure μ (p.1 - p.2)‖ₑ) := by
        refine lintegral_mono (fun p => ?_)
        simp only [hh_def, hh'_def, enorm_mul, RCLike.enorm_conj, map_mul]
        have e1 := gG_enorm_le G p.1
        have e2 := gG_enorm_le G' p.2
        calc ‖phiLoc n R c p.1‖ₑ * ‖gG G p.1‖ₑ * (‖phiLoc n R c' p.2‖ₑ * ‖gG G' p.2‖ₑ) *
              ‖ftMeasure μ (p.1 - p.2)‖ₑ
            ≤ ‖phiLoc n R c p.1‖ₑ * A * (‖phiLoc n R c' p.2‖ₑ * A') * ‖ftMeasure μ (p.1 - p.2)‖ₑ := by
              gcongr
          _ = _ := by ring
    _ = A * A' * ∫⁻ y, ∫⁻ y', ‖phiLoc n R c y‖ₑ * ‖phiLoc n R c' y'‖ₑ * ‖ftMeasure μ (y - y')‖ₑ := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top hA hA'), Measure.volume_eq_prod,
          lintegral_prod _ hmeas]

/-- `∫ ‖φ‖`. -/
noncomputable def M0 (n : ℕ) : ℝ := ∫ u, ‖phi n u‖

/-- `∫ ‖u‖ ‖φ(u)‖`. -/
noncomputable def M1 (n : ℕ) : ℝ := ∫ u : E n, ‖u‖ * ‖phi n u‖

lemma M0_nonneg : 0 ≤ M0 n := integral_nonneg (fun _ => norm_nonneg _)

lemma M1_nonneg : 0 ≤ M1 n := integral_nonneg (fun _ => by positivity)

lemma phiLoc_lint (hR : 0 < R) (c : E n) :
    ∫⁻ y, ‖phiLoc n R c y‖ₑ = ENNReal.ofReal (R ^ n * M0 n) := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (phiLoc_integrable hR), phiLoc_L1 hR, M0]

lemma phiLoc_mom_lint (hR : 0 < R) (c : E n) :
    ∫⁻ y, ENNReal.ofReal ‖y - c‖ * ‖phiLoc n R c y‖ₑ = ENNReal.ofReal (R ^ (n + 1) * M1 n) := by
  rw [M1, ← phiLoc_moment (c := c) hR, ofReal_integral_eq_lintegral_ofReal (phiLoc_moment_integrable hR)
    (Eventually.of_forall (fun _ => by positivity))]
  congr 1; ext y
  rw [ENNReal.ofReal_mul (norm_nonneg _)]; simp only [ofReal_norm]

omit [IsFiniteMeasure μ] in
lemma kern_le (hR : 0 < R) (c c' : E n) (B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hpt : ∀ y y' : E n, ‖ftMeasure μ (y - y')‖ ≤ B + T * (‖y - c‖ + ‖y' - c'‖)) :
    ∫⁻ y, ∫⁻ y', ‖phiLoc n R c y‖ₑ * ‖phiLoc n R c' y'‖ₑ * ‖ftMeasure μ (y - y')‖ₑ ≤
      ENNReal.ofReal (B * (R ^ n * M0 n) ^ 2 + T * (2 * R ^ (2 * n + 1) * M0 n * M1 n)) := by
  set a : E n → ℝ≥0∞ := fun y => ‖phiLoc n R c y‖ₑ
  set a' : E n → ℝ≥0∞ := fun y => ‖phiLoc n R c' y‖ₑ
  set b : E n → ℝ≥0∞ := fun y => ENNReal.ofReal ‖y - c‖ * ‖phiLoc n R c y‖ₑ
  set b' : E n → ℝ≥0∞ := fun y => ENNReal.ofReal ‖y - c'‖ * ‖phiLoc n R c' y‖ₑ
  have ha : Measurable a := (phiLoc_contDiff (c := c) (R := R)).continuous.measurable.enorm
  have ha' : Measurable a' := (phiLoc_contDiff (c := c') (R := R)).continuous.measurable.enorm
  have hb : Measurable b :=
    ((continuous_id.sub continuous_const).norm.measurable.ennreal_ofReal).mul ha
  have hb' : Measurable b' :=
    ((continuous_id.sub continuous_const).norm.measurable.ennreal_ofReal).mul ha'
  set β := ENNReal.ofReal B
  set τ := ENNReal.ofReal T
  have hpt' : ∀ y y', a y * a' y' * ‖ftMeasure μ (y - y')‖ₑ ≤
      β * a y * a' y' + (τ * b y * a' y' + τ * a y * b' y') := by
    intro y y'
    have h1 : ‖ftMeasure μ (y - y')‖ₑ ≤ β + τ * (ENNReal.ofReal ‖y - c‖ + ENNReal.ofReal ‖y' - c'‖) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
        ← ENNReal.ofReal_mul hT, ← ENNReal.ofReal_add hB (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hpt y y')
    calc a y * a' y' * ‖ftMeasure μ (y - y')‖ₑ
        ≤ a y * a' y' * (β + τ * (ENNReal.ofReal ‖y - c‖ + ENNReal.ofReal ‖y' - c'‖)) := by
          gcongr
      _ = _ := by simp only [a, a', b, b']; ring
  calc ∫⁻ y, ∫⁻ y', a y * a' y' * ‖ftMeasure μ (y - y')‖ₑ
      ≤ ∫⁻ y, ∫⁻ y', β * a y * a' y' + (τ * b y * a' y' + τ * a y * b' y') :=
        lintegral_mono (fun y => lintegral_mono (fun y' => hpt' y y'))
    _ = β * (∫⁻ y, a y) * (∫⁻ y, a' y) +
          (τ * (∫⁻ y, b y) * (∫⁻ y, a' y) + τ * (∫⁻ y, a y) * (∫⁻ y, b' y)) := by
        have e : ∀ y, ∫⁻ y', β * a y * a' y' + (τ * b y * a' y' + τ * a y * b' y') =
            β * a y * (∫⁻ y', a' y') + (τ * b y * (∫⁻ y', a' y') + τ * a y * ∫⁻ y', b' y') := by
          intro y
          rw [lintegral_add_left (ha'.const_mul _), lintegral_add_left (ha'.const_mul _),
            lintegral_const_mul _ ha', lintegral_const_mul _ ha', lintegral_const_mul _ hb']
        simp_rw [e]
        rw [lintegral_add_left ((ha.const_mul _).mul_const _),
          lintegral_add_left (((hb.const_mul _)).mul_const _),
          lintegral_mul_const _ (ha.const_mul _), lintegral_mul_const _ (hb.const_mul _),
          lintegral_mul_const _ (ha.const_mul _), lintegral_const_mul _ ha,
          lintegral_const_mul _ hb, lintegral_const_mul _ ha]
    _ = _ := by
        simp only [a, a', b, b']
        rw [phiLoc_lint hR, phiLoc_lint hR, phiLoc_mom_lint hR, phiLoc_mom_lint hR]
        have h0 := M0_nonneg (n := n)
        have h1 := M1_nonneg (n := n)
        simp only [β, τ]
        rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul hT, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul hT, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

lemma sig_pt (m : ℕ) (hm : 0 < m) (Cs : ℝ)
    (hdec : ∀ z : E n, 1 ≤ ‖z‖ → ‖ftMeasure μ z‖ ^ m * ‖z‖ ≤ Cs) (c c' : E n) (Q : ℝ) (hQ : 1 ≤ Q)
    (hw2 : 2 ≤ ‖c - c'‖) (hQw : Q ^ m ≤ ‖c - c'‖) (y y' : E n) :
    ‖ftMeasure μ (y - y')‖ ≤ max 1 (2 * Cs) / Q +
      4 * (μ).real univ / ‖c - c'‖ * (‖y - c‖ + ‖y' - c'‖) := by
  set w := c - c'
  set d := ‖y - c‖ + ‖y' - c'‖
  set D := max 1 (2 * Cs)
  set s := (μ).real univ
  have hs : 0 ≤ s := measureReal_nonneg
  have hw0 : 0 < ‖w‖ := by linarith
  have hd0 : 0 ≤ d := by positivity
  have hD1 : 1 ≤ D := le_max_left _ _
  have hDQ : 0 ≤ D / Q := by positivity
  have hsig := sig_norm_le (μ := μ) (y - y')
  by_cases hd : d * 2 ≤ ‖w‖
  · have hz : ‖w‖ / 2 ≤ ‖y - y'‖ := by
      have e : y - y' = w + (y - c) - (y' - c') := by simp only [w]; abel
      have := norm_sub_norm_le w (-(y - c) + (y' - c'))
      have h2 : ‖-(y - c) + (y' - c')‖ ≤ d := (norm_add_le _ _).trans (by rw [norm_neg])
      have e2 : w - (-(y - c) + (y' - c')) = y - y' := by rw [e]; abel
      rw [e2] at this
      linarith
    have hz1 : 1 ≤ ‖y - y'‖ := by linarith
    have hk := hdec (y - y') hz1
    set a := ‖ftMeasure μ (y - y')‖
    have ha : 0 ≤ a := norm_nonneg _
    have hCs : 0 ≤ Cs := le_trans (by positivity) hk
    have h1 : a ^ m * ‖w‖ ≤ 2 * Cs := by
      have : a ^ m * (‖w‖ / 2) ≤ Cs :=
        le_trans (mul_le_mul_of_nonneg_left hz (by positivity)) hk
      linarith
    have h2 : (a * Q) ^ m ≤ D ^ m := by
      rw [mul_pow]
      calc a ^ m * Q ^ m ≤ a ^ m * ‖w‖ := mul_le_mul_of_nonneg_left hQw (by positivity)
        _ ≤ 2 * Cs := h1
        _ ≤ D := le_max_right _ _
        _ ≤ D ^ m := le_self_pow₀ hD1 hm.ne'
    have h3 : a * Q ≤ D :=
      (pow_le_pow_iff_left₀ (by positivity) (by positivity) hm.ne').1 h2
    have h4 : a ≤ D / Q := by rw [le_div_iff₀ (by linarith)]; exact h3
    have : 0 ≤ 4 * s / ‖w‖ * d := by positivity
    linarith
  · rw [not_le] at hd
    have : s ≤ 4 * s / ‖w‖ * d := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hw0]
      nlinarith
    linarith

end TaoBR.Tao49.PartW1
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise
namespace TaoBR.Tao49.PartW1
variable {n : ℕ} {R : ℝ} {c : E n}
variable {n : ℕ} {R : ℝ} {μ : Measure (E n)} [IsFiniteMeasure μ]
variable {N : ℕ} {x : Fin N → E n}
omit [IsFiniteMeasure μ] in
lemma K_enorm_center (c v : E n) : ‖Kker n R c v‖ₑ = ‖Kker n R 0 v‖ₑ := by
  simp only [Kker, enorm_mul]
  congr 1
  rw [← ofReal_norm, ← ofReal_norm, Circle.norm_coe, Circle.norm_coe]

lemma Fop_diag (hR : 1 ≤ R) (c : E n)
    {G : E n → ℂ} (hGm : Measurable G) :
    ∫⁻ ω, ‖Fop n R c G ω‖ₑ ^ 2 ∂(μ) ≤ ∫⁻ η, ‖G η‖ₑ ^ 2 * Wt μ R η := by
  have hR0 : 0 < R := by linarith
  have hKm : Measurable (fun p : E n × E n => ‖Kker n R c (p.1 - p.2)‖ₑ) :=
    (K_continuous.measurable.comp ((measurable_fst).sub
      measurable_snd)).enorm
  have hpt : ∀ ω : E n, ‖Fop n R c G ω‖ₑ ^ 2 ≤
      ∫⁻ η, ‖Kker n R c (ω - η)‖ₑ * ‖G η‖ₑ ^ 2 := by
    intro ω
    have h1 : ‖Fop n R c G ω‖ₑ ≤ ∫⁻ η, ‖Kker n R c (ω - η)‖ₑ * ‖G η‖ₑ := by
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      simp_rw [enorm_mul]
    have hK1 : ∫⁻ η, ‖Kker n R c (ω - η)‖ₑ = 1 := by
      rw [lintegral_sub_left_eq_self (fun v => ‖Kker n R c v‖ₑ) ω]
      exact K_lintegral hR0 c
    have hKm1 : Measurable (fun η : E n => ‖Kker n R c (ω - η)‖ₑ) :=
      (K_continuous.measurable.comp (measurable_const.sub measurable_id)).enorm
    calc ‖Fop n R c G ω‖ₑ ^ 2
        ≤ (∫⁻ η, ‖Kker n R c (ω - η)‖ₑ * ‖G η‖ₑ) ^ 2 := by gcongr
      _ ≤ (∫⁻ η, ‖Kker n R c (ω - η)‖ₑ) * ∫⁻ η, ‖Kker n R c (ω - η)‖ₑ * ‖G η‖ₑ ^ 2 :=
          lintegral_cs _ hKm1.aemeasurable hGm.enorm.aemeasurable
      _ = _ := by rw [hK1, one_mul]
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  rw [lintegral_lintegral_swap (hKm.mul ((hGm.comp measurable_snd).enorm.pow_const 2)).aemeasurable]
  refine lintegral_congr (fun η => ?_)
  rw [lintegral_mul_const' _ _ (by simp), mul_comm, Wt]
  simp_rw [K_enorm_center c]

/-- The off-diagonal constant. -/
noncomputable def Cst (μ : Measure (E n)) (Cs : ℝ) : ℝ :=
  max 1 (2 * Cs) * M0 n ^ 2 + 8 * (μ).real univ * M0 n * M1 n

lemma kern_sparse (hn : 1 ≤ n) (m : ℕ) (hm : 0 < m) (Cs : ℝ)
    (hdec : ∀ z : E n, 1 ≤ ‖z‖ → ‖ftMeasure μ z‖ ^ m * ‖z‖ ≤ Cs) (hR : 1 ≤ R) (N : ℕ) (hN : 2 ≤ N)
    (c c' : E n) (hw : (R * N) ^ (3 * n * m + 3 * n + 3) ≤ ‖c - c'‖) :
    ∫⁻ y, ∫⁻ y', ‖phiLoc n R c y‖ₑ * ‖phiLoc n R c' y'‖ₑ * ‖ftMeasure μ (y - y')‖ₑ ≤
      ENNReal.ofReal (Cst μ Cs / (N * R ^ n)) := by
  have hR0 : 0 < R := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set X := R * (N : ℝ) with hX
  have hX2 : 2 ≤ X := by nlinarith
  have hX1 : 1 ≤ X := by linarith
  set C0 := 3 * n * m + 3 * n + 3
  set w := c - c'
  set Q := R ^ (3 * n) * (N : ℝ) with hQ
  have hQ1 : 1 ≤ Q := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR) hN1
  have hw2 : 2 ≤ ‖w‖ := le_trans (le_trans hX2 (le_self_pow₀ hX1 (by omega))) hw
  have hw0 : 0 < ‖w‖ := by linarith
  have hQw : Q ^ m ≤ ‖w‖ := by
    calc Q ^ m = R ^ (3 * n * m) * (N : ℝ) ^ m := by rw [hQ, mul_pow, ← pow_mul]
      _ ≤ R ^ (3 * n * m) * (N : ℝ) ^ (3 * n * m) := by
          gcongr
          nlinarith
      _ = X ^ (3 * n * m) := by rw [hX, mul_pow]
      _ ≤ X ^ C0 := pow_le_pow_right₀ hX1 (by omega)
      _ ≤ ‖w‖ := hw
  have hRw : R ^ (3 * n + 1) * N ≤ ‖w‖ := by
    calc R ^ (3 * n + 1) * (N : ℝ) ≤ R ^ (3 * n + 1) * (N : ℝ) ^ (3 * n + 1) := by
          gcongr; exact le_self_pow₀ hN1 (by omega)
      _ = X ^ (3 * n + 1) := by rw [hX, mul_pow]
      _ ≤ X ^ C0 := pow_le_pow_right₀ hX1 (by omega)
      _ ≤ ‖w‖ := hw
  set D := max 1 (2 * Cs)
  set s := (μ).real univ
  have hs : 0 ≤ s := measureReal_nonneg
  have hD : 0 ≤ D := le_trans zero_le_one (le_max_left _ _)
  have hk := kern_le hR0 c c' (D / Q) (4 * s / ‖w‖) (by positivity) (by positivity)
    (sig_pt m hm Cs hdec c c' Q hQ1 hw2 hQw)
  refine hk.trans (ENNReal.ofReal_le_ofReal ?_)
  have h0 := M0_nonneg (n := n)
  have h1 := M1_nonneg (n := n)
  have hN0 : (0 : ℝ) < N := by linarith
  have hRn : (0 : ℝ) < R ^ n := by positivity
  have t1 : D / Q * (R ^ n * M0 n) ^ 2 = D * M0 n ^ 2 / (N * R ^ n) := by
    rw [hQ, mul_pow, ← pow_mul]
    have : R ^ (3 * n) = R ^ n * R ^ n * R ^ n := by ring
    rw [this]; field_simp; ring
  have t2 : 4 * s / ‖w‖ * (2 * R ^ (2 * n + 1) * M0 n * M1 n) ≤
      8 * s * M0 n * M1 n / (N * R ^ n) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hw0 (by positivity)]
    have e : R ^ (3 * n + 1) = R ^ (2 * n + 1) * R ^ n := by ring
    rw [e] at hRw
    have := mul_le_mul_of_nonneg_left hRw (by positivity : 0 ≤ 8 * s * M0 n * M1 n)
    nlinarith
  rw [t1, Cst, add_div]
  linarith

omit [IsFiniteMeasure μ] in
lemma Cst_nonneg (μ : Measure (E n)) (Cs : ℝ) : 0 ≤ Cst μ Cs := by
  unfold Cst
  have := M0_nonneg (n := n)
  have := M1_nonneg (n := n)
  have : 0 ≤ (μ).real univ := measureReal_nonneg
  have : 0 ≤ max 1 (2 * Cs) := le_trans zero_le_one (le_max_left _ _)
  positivity

lemma Top_L2_core (hn : 1 ≤ n) (m : ℕ) (hm : 0 < m) (Cs : ℝ)
    (hdec : ∀ z : E n, 1 ≤ ‖z‖ → ‖ftMeasure μ z‖ ^ m * ‖z‖ ≤ Cs) (hR : 1 ≤ R)
    (V : ℝ) (hV : 0 ≤ V)
    (hsp : ∀ i j, i ≠ j → (R * N) ^ (3 * n * m + 3 * n + 3) ≤ ‖x i - x j‖)
    (G : Fin N → E n → ℂ) (hGi : ∀ i, Integrable (G i)) (hGs : ∀ i, StronglyMeasurable (G i))
    (hL2 : ∀ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 ≠ ⊤)
    (hDf : ∀ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 * Wt μ R η ≠ ⊤)
    (hL1 : ∀ i, (∫⁻ η, ‖G i η‖ₑ) ^ 2 ≤ ENNReal.ofReal V * ∫⁻ η, ‖G i η‖ₑ ^ 2) :
    ∫⁻ ω, ‖Top R x G ω‖ₑ ^ 2 ∂(μ) ≤
      (∑ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 * Wt μ R η) +
        ENNReal.ofReal (Cst μ Cs * V / R ^ n) * ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 := by
  have hR0 : 0 < R := by linarith
  set σ := μ
  set F : Fin N → E n → ℂ := fun i ω => Fop n R (x i) (G i) ω with hF
  have hTop : ∀ ω, Top R x G ω = ∑ i, F i ω := fun ω => rfl
  have hFm : ∀ i, StronglyMeasurable (F i) := by
    intro i
    refine StronglyMeasurable.integral_prod_right (f := fun (ω : E n) (η : E n) =>
      Kker n R (x i) (ω - η) * G i η) ?_
    exact (K_continuous.comp ((continuous_fst).sub
      continuous_snd)).stronglyMeasurable.mul ((hGs i).comp_measurable measurable_snd)
  set Mb : Fin N → ℝ := fun i => R ^ n * MPhi n * ∫ η, ‖G i η‖
  have hFb : ∀ i ω, ‖F i ω‖ ≤ Mb i := by
    intro i ω
    refine (norm_integral_le_of_norm_le ((hGi i).norm.const_mul (R ^ n * MPhi n))
      (Eventually.of_forall (fun η => ?_))).trans (le_of_eq (integral_const_mul _ _))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (K_norm_le hR0 _) (norm_nonneg _)
  have hPint : ∀ i j, Integrable (fun ω => F i ω * conj (F j ω)) σ := by
    intro i j
    refine Integrable.of_bound ((hFm i).mul (Complex.continuous_conj.comp_stronglyMeasurable
      (hFm j))).aestronglyMeasurable (Mb i * Mb j) (Eventually.of_forall (fun ω => ?_))
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul (hFb i ω) (hFb j ω) (norm_nonneg _) ((norm_nonneg _).trans (hFb i ω))
  have hsq : ∀ ω, ‖Top R x G ω‖ ^ 2 = ∑ i, ∑ j, (F i ω * conj (F j ω)).re := by
    intro ω
    rw [hTop]
    have h1 : ((‖∑ i, F i ω‖ ^ 2 : ℝ) : ℂ) = ∑ i, ∑ j, F i ω * conj (F j ω) := by
      rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    have := congrArg Complex.re h1
    simpa only [Complex.ofReal_re, Complex.re_sum] using this
  have hint : ∀ i j, Integrable (fun ω => (F i ω * conj (F j ω)).re) σ := fun i j => (hPint i j).re
  have hLHS : ∫⁻ ω, ‖Top R x G ω‖ₑ ^ 2 ∂σ =
      ENNReal.ofReal (∑ i, ∑ j, (∫ ω, F i ω * conj (F j ω) ∂σ).re) := by
    have e : ∀ ω, ‖Top R x G ω‖ₑ ^ 2 =
        ENNReal.ofReal (∑ i, ∑ j, (F i ω * conj (F j ω)).re) := by
      intro ω; rw [← hsq, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finsetSum _ (fun j _ => hint i j)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact integral_re (hPint i j)
    · exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))
    · exact Eventually.of_forall (fun ω => by simp only [Pi.zero_apply]; rw [← hsq]; positivity)
  set a : Fin N → ℝ := fun i => (∫⁻ η, ‖G i η‖ₑ).toReal
  set b : Fin N → ℝ := fun i => (∫⁻ η, ‖G i η‖ₑ ^ 2).toReal
  have hA : ∀ i, ∫⁻ η, ‖G i η‖ₑ = ENNReal.ofReal (a i) :=
    fun i => (ENNReal.ofReal_toReal (hGi i).2.ne).symm
  have hB : ∀ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 = ENNReal.ofReal (b i) :=
    fun i => (ENNReal.ofReal_toReal (hL2 i)).symm
  have ha0 : ∀ i, 0 ≤ a i := fun i => ENNReal.toReal_nonneg
  have hb0 : ∀ i, 0 ≤ b i := fun i => ENNReal.toReal_nonneg
  have hab : ∀ i, a i ^ 2 ≤ V * b i := by
    intro i
    have := hL1 i
    rw [hA, hB, ← ENNReal.ofReal_pow (ha0 i), ← ENNReal.ofReal_mul hV] at this
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hV (hb0 i))).1 this
  set d : Fin N → ℝ := fun i => (∫⁻ η, ‖G i η‖ₑ ^ 2 * Wt μ R η).toReal
  have hDd : ∀ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 * Wt μ R η = ENNReal.ofReal (d i) :=
    fun i => (ENNReal.ofReal_toReal (hDf i)).symm
  have hd0 : ∀ i, 0 ≤ d i := fun i => ENNReal.toReal_nonneg
  have hdiag : ∀ i, (∫ ω, F i ω * conj (F i ω) ∂σ).re ≤ d i := by
    intro i
    have hre : ∫ ω, (F i ω * conj (F i ω)).re ∂σ = (∫ ω, F i ω * conj (F i ω) ∂σ).re :=
      integral_re (hPint i i)
    rw [← hre]
    have e : ∀ ω, (F i ω * conj (F i ω)).re = ‖F i ω‖ ^ 2 := by
      intro ω; rw [Complex.mul_conj']; norm_cast
    simp_rw [e]
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun ω => ‖F i ω‖ ^ 2)
      (Eventually.of_forall (fun _ => by positivity))
      ((hFm i).measurable.norm.pow_const 2).aestronglyMeasurable]
    have e2 : ∀ ω, ENNReal.ofReal (‖F i ω‖ ^ 2) = ‖F i ω‖ₑ ^ 2 := by
      intro ω; rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    simp_rw [e2]
    have hd := Fop_diag (μ := μ) hR (x i) (hGs i).measurable
    rw [hDd i] at hd
    calc _ ≤ (ENNReal.ofReal (d i)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
      _ = _ := ENNReal.toReal_ofReal (hd0 i)
  have hC := Cst_nonneg μ Cs
  have hRn : (0 : ℝ) < R ^ n := by positivity
  have hoff : ∀ i j, i ≠ j →
      (∫ ω, F i ω * conj (F j ω) ∂σ).re ≤ Cst μ Cs / (N * R ^ n) * (a i * a j) := by
    intro i j hij
    have hN : 2 ≤ N := by
      have := i.2; have := j.2; have : (i : ℕ) ≠ j := Fin.val_ne_of_ne hij; omega
    have hk := kern_sparse hn m hm Cs hdec hR N hN (x i) (x j) (hsp i j hij)
    have ho := Fop_offdiag (μ := μ) hR0 (x i) (x j) (hGi i) (hGi j) (hGs i) (hGs j)
    rw [hA, hA] at ho
    have h2 := ho.trans (mul_le_mul_of_nonneg_left hk (by positivity))
    have hai := ha0 i
    have haj := ha0 j
    have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [← ENNReal.ofReal_mul hai, ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm] at h2
    have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
    calc _ ≤ ‖∫ ω, F i ω * conj (F j ω) ∂σ‖ := Complex.re_le_norm _
      _ ≤ _ := h3.trans (le_of_eq (by ring))
  have hsum : ∑ i, ∑ j, (∫ ω, F i ω * conj (F j ω) ∂σ).re ≤
      ∑ i, ∑ j, ((if i = j then d i else 0) + Cst μ Cs / (N * R ^ n) * (a i * a j)) := by
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      have := hdiag i
      have : 0 ≤ Cst μ Cs / (N * R ^ n) * (a i * a i) := by
        have := ha0 i; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; positivity
      linarith
    · simp only [hij, if_false, zero_add]
      exact hoff i j hij
  have hcomb : ∑ i, ∑ j, ((if i = j then d i else 0) + Cst μ Cs / (N * R ^ n) * (a i * a j)) =
      ∑ i, d i + Cst μ Cs / (N * R ^ n) * (∑ i, a i) ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.mul_sum, sq, Finset.sum_mul_sum]
  have hCS : Cst μ Cs / (N * R ^ n) * (∑ i, a i) ^ 2 ≤ Cst μ Cs * V / R ^ n * ∑ i, b i := by
    have h1 : (∑ i, a i) ^ 2 ≤ N * ∑ i, a i ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
    have h2 : ∑ i, a i ^ 2 ≤ V * ∑ i, b i := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun i _ => hab i)
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      calc Cst μ Cs * (∑ i, a i) ^ 2 ≤ Cst μ Cs * (N * (V * ∑ i, b i)) := by
            gcongr; exact h1.trans (by gcongr)
        _ = _ := by field_simp
  have hbn : 0 ≤ ∑ i, b i := Finset.sum_nonneg (fun i _ => hb0 i)
  have hdn : 0 ≤ ∑ i, d i := Finset.sum_nonneg (fun i _ => hd0 i)
  rw [hLHS]
  calc ENNReal.ofReal (∑ i, ∑ j, (∫ ω, F i ω * conj (F j ω) ∂σ).re)
      ≤ ENNReal.ofReal (∑ i, d i + Cst μ Cs * V / R ^ n * ∑ i, b i) := by
        apply ENNReal.ofReal_le_ofReal
        linarith [hsum, hcomb, hCS]
    _ = _ := by
        rw [ENNReal.ofReal_add hdn (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun i _ => hd0 i),
          ENNReal.ofReal_sum_of_nonneg (fun i _ => hb0 i)]
        simp only [← hDd, ← hB]
        rfl

lemma l1_l2_ball (g : E n → ℂ) (hgm : Measurable g)
    (hg : ∀ η, η ∉ closedBall (0 : E n) 2 → g η = 0) :
    (∫⁻ η, ‖g η‖ₑ) ^ 2 ≤
      ENNReal.ofReal ((volume : Measure (E n)).real (closedBall 0 2)) * ∫⁻ η, ‖g η‖ₑ ^ 2 := by
  set a : E n → ℝ≥0∞ := (closedBall (0 : E n) 2).indicator 1
  have ha : Measurable a := measurable_one.indicator measurableSet_closedBall
  have hab : ∀ η, a η * ‖g η‖ₑ = ‖g η‖ₑ := by
    intro η
    by_cases h : η ∈ closedBall (0 : E n) 2
    · simp [a, indicator_of_mem h]
    · simp [hg η h]
  have hb : ∀ η, a η * ‖g η‖ₑ ^ 2 ≤ ‖g η‖ₑ ^ 2 := by
    intro η
    by_cases h : η ∈ closedBall (0 : E n) 2
    · simp [a, indicator_of_mem h]
    · simp [hg η h]
  have h := lintegral_cs (volume : Measure (E n)) (a := a) (b := fun η => ‖g η‖ₑ)
    ha.aemeasurable hgm.enorm.aemeasurable
  simp only [hab] at h
  have h1 : ∫⁻ η, a η = ENNReal.ofReal ((volume : Measure (E n)).real (closedBall 0 2)) := by
    rw [lintegral_indicator_one measurableSet_closedBall,
      ofReal_measureReal (isCompact_closedBall _ _).measure_lt_top.ne]
  rw [h1] at h
  exact h.trans (by gcongr; exact hb _)

/-! ## From power decay to the sphere-style decay -/
lemma decay_conv {f : E n → ℂ} {C c : ℝ} (hc : 0 < c)
    (h : ∀ x : E n, ‖f x‖ ≤ C * (1 + ‖x‖) ^ (-c)) :
    ∃ k : ℕ, 0 < k ∧ ∃ Cs : ℝ, ∀ z : E n, 1 ≤ ‖z‖ → ‖f z‖ ^ k * ‖z‖ ≤ Cs := by
  have hC : 0 ≤ C := by
    have := h 0
    simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  set k := ⌈1 / c⌉₊ with hk
  have hk0 : 0 < k := Nat.ceil_pos.2 (by positivity)
  have hkc : 1 ≤ c * k := by
    have := Nat.le_ceil (1 / c)
    rw [← hk] at this
    rw [div_le_iff₀ hc] at this
    linarith
  refine ⟨k, hk0, C ^ k, fun z hz => ?_⟩
  set t := ‖z‖
  have ht : 0 ≤ t := norm_nonneg _
  have h1t : 1 ≤ 1 + t := by linarith
  have hb : 0 ≤ (1 + t) ^ (-c) := Real.rpow_nonneg (by linarith) _
  have h1 : ‖f z‖ ^ k ≤ C ^ k * (1 + t)⁻¹ := by
    calc ‖f z‖ ^ k ≤ (C * (1 + t) ^ (-c)) ^ k := pow_le_pow_left₀ (norm_nonneg _) (h z) k
      _ = C ^ k * (1 + t) ^ (-c * k) := by
          rw [mul_pow, Real.rpow_mul_natCast (by linarith)]
      _ ≤ C ^ k * (1 + t) ^ (-1 : ℝ) := by
          gcongr
          · linarith
      _ = C ^ k * (1 + t)⁻¹ := by rw [Real.rpow_neg_one]
  have hCk : 0 ≤ C ^ k := by positivity
  calc ‖f z‖ ^ k * t ≤ C ^ k * (1 + t)⁻¹ * t := mul_le_mul_of_nonneg_right h1 ht
    _ = C ^ k * (t / (1 + t)) := by ring
    _ ≤ C ^ k * 1 := by
        gcongr
        rw [div_le_one (by linarith)]; linarith
    _ = C ^ k := mul_one _

/-! ## The main bound -/
/-- **W1 (Lemma 3.2, the weighted `L²` bound).** Verbatim restatement of the Blueprint's
`top_L2w`. -/
theorem top_L2w {n : ℕ} (hn : 2 ≤ n) {μ : Measure (E n)} {S : Set (E n)} (hμ : DecayMeasure μ S) :
    ∃ C0 : ℕ, 3 * n + 3 ≤ C0 ∧ ∃ A2 : ℝ, 0 ≤ A2 ∧
      ∀ R : ℝ, 1 ≤ R → ∀ (N : ℕ) (x : Fin N → E n), IsSparse (C0 : ℝ) R x →
        ∀ G : Fin N → E n → ℂ, (∀ i, Measurable (G i)) → (∀ i, ∃ B : ℝ, ∀ η, ‖G i η‖ ≤ B) →
          (∀ i η, η ∉ closedBall (0 : E n) 2 → G i η = 0) →
          ∫⁻ ω, ‖Top R x G ω‖ₑ ^ (2 : ℝ) ∂μ ≤
            ENNReal.ofReal A2 * ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ (2 : ℝ) *
              (Wt μ R η + ENNReal.ofReal (R ^ (-(n : ℝ)))) := by
  have := hμ.finite
  obtain ⟨Cd, c, hc, hdec0⟩ := hμ.decay
  obtain ⟨m, hm, Cs, hdec⟩ := decay_conv hc hdec0
  set V := (volume : Measure (E n)).real (closedBall 0 2)
  have hV : 0 ≤ V := measureReal_nonneg
  have hCst := Cst_nonneg μ Cs
  refine ⟨3 * n * m + 3 * n + 3, by omega, 1 + Cst μ Cs * V, by positivity, ?_⟩
  intro R hR N x hsp G hGm _hGb hG0
  have hR0 : 0 < R := by linarith
  simp only [ENNReal.rpow_two]
  set fl := ENNReal.ofReal (R ^ (-(n : ℝ))) with hfl_def
  have hfl : R ^ (-(n : ℝ)) = 1 / R ^ n := by
    rw [Real.rpow_neg hR0.le, Real.rpow_natCast, one_div]
  have hfl0 : fl ≠ 0 := by
    rw [hfl_def, hfl]; simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hsplit : ∀ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 * (Wt μ R η + fl) =
      (∫⁻ η, ‖G i η‖ₑ ^ 2 * Wt μ R η) + fl * ∫⁻ η, ‖G i η‖ₑ ^ 2 := by
    intro i
    simp_rw [mul_add]
    rw [lintegral_add_right _ (((hGm i).enorm.pow_const 2).mul_const _),
      lintegral_mul_const _ ((hGm i).enorm.pow_const 2), mul_comm fl]
  have hA0 : ENNReal.ofReal (1 + Cst μ Cs * V) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  by_cases hfin : ∀ i, (∫⁻ η, ‖G i η‖ₑ ^ 2 * Wt μ R η) ≠ ⊤ ∧ (∫⁻ η, ‖G i η‖ₑ ^ 2) ≠ ⊤
  swap
  · push Not at hfin
    obtain ⟨i, hi⟩ := hfin
    have htop : ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 * (Wt μ R η + fl) = ⊤ := by
      refine ENNReal.sum_eq_top.2 ⟨i, Finset.mem_univ _, ?_⟩
      rw [hsplit i]
      by_cases h1 : (∫⁻ η, ‖G i η‖ₑ ^ 2 * Wt μ R η) = ⊤
      · rw [h1, top_add]
      · rw [hi h1, ENNReal.mul_top hfl0, add_top]
    rw [htop, ENNReal.mul_top hA0]
    exact le_top
  have hL1 : ∀ i, (∫⁻ η, ‖G i η‖ₑ) ^ 2 ≤ ENNReal.ofReal V * ∫⁻ η, ‖G i η‖ₑ ^ 2 :=
    fun i => l1_l2_ball (G i) (hGm i) (hG0 i)
  have hGi : ∀ i, Integrable (G i) := by
    intro i
    refine ⟨(hGm i).aestronglyMeasurable, ?_⟩
    have h1 : (∫⁻ η, ‖G i η‖ₑ) ^ 2 < ⊤ :=
      (hL1 i).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin i).2.lt_top)
    have h2 : ∫⁻ η, ‖G i η‖ₑ < ⊤ := by
      by_contra h
      rw [not_lt, top_le_iff] at h
      rw [h] at h1; simp at h1
    exact h2
  have hsp' : ∀ i j, i ≠ j → (R * N) ^ (3 * n * m + 3 * n + 3) ≤ ‖x i - x j‖ := by
    intro i j h
    have := hsp i j h
    rwa [Real.rpow_natCast, Real.rpow_natCast, ← mul_pow, dist_eq_norm] at this
  refine (Top_L2_core (by omega) m hm Cs hdec hR V hV hsp' G hGi
    (fun i => (hGm i).stronglyMeasurable) (fun i => (hfin i).2) (fun i => (hfin i).1) hL1).trans ?_
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have e1 : ENNReal.ofReal (Cst μ Cs * V / R ^ n) = ENNReal.ofReal (Cst μ Cs * V) * fl := by
    rw [hfl_def, hfl, ← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  rw [e1, ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
  set X := ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 * Wt μ R η
  set Y := ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ 2
  set c := ENNReal.ofReal (Cst μ Cs * V)
  calc X + c * fl * Y ≤ (X + c * fl * Y) + (c * X + fl * Y) := le_self_add
    _ = (1 + c) * (X + fl * Y) := by ring

end TaoBR.Tao49.PartW1
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
/-! ## Generic ε-removal (Lemma 3.2, the p. 7 reduction, Theorem 1.2) for a decaying measure -/
alias top_L2w := TaoBR.Tao49.PartW1.top_L2w

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise
namespace TaoBR.Tao49.PartW2
/-!
# Part W2 of the Theorem 4.9 Blueprint: `smoothed_of_restrMu`, `sparse_of_restrMu`
(port of `proofs/parab/PartB.lean`)

The thickened estimate is replaced by the smoothed weight `Wt μ R` plus the floor `R^{-n}`: the
interpolation runs in `L^q(volume.withDensity (Wt μ R + R^{-n}))`.
-/
/-! ## The bump `Φ` and `φ = 𝓕⁻ Φ` -/
noncomputable abbrev PhiC (n : ℕ) (v : E n) : ℂ := (Phi n v : ℂ)

noncomputable def MPhi (n : ℕ) : ℝ := 1 / (volume : Measure (E n)).real (closedBall 0 (1 / 32))

lemma Phi_nonneg (n : ℕ) (v : E n) : 0 ≤ Phi n v := (bump n).nonneg_normed v

lemma Phi_le (n : ℕ) (v : E n) : Phi n v ≤ MPhi n :=
  (bump n).normed_le_div_measure_closedBall_rIn volume v

lemma Phi_support (n : ℕ) {v : E n} (h : Phi n v ≠ 0) : ‖v‖ < 1 / 16 := by
  have : v ∈ Function.support ((bump n).normed volume) := h
  rw [(bump n).support_normed_eq, mem_ball_zero_iff] at this
  exact this

lemma Phi_integral (n : ℕ) : ∫ v, Phi n v = 1 := (bump n).integral_normed

lemma PhiC_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (PhiC n) :=
  Complex.ofRealCLM.contDiff.comp (bump n).contDiff_normed

lemma PhiC_hasCompactSupport (n : ℕ) : HasCompactSupport (PhiC n) :=
  (bump n).hasCompactSupport_normed.comp_left Complex.ofReal_zero

noncomputable def PhiS (n : ℕ) : 𝓢(E n, ℂ) :=
  (PhiC_hasCompactSupport n).toSchwartzMap (PhiC_contDiff n)

/-- `φ = 𝓕⁻ Φ` as a Schwartz map. -/
noncomputable def phiS (n : ℕ) : 𝓢(E n, ℂ) := 𝓕⁻ (PhiS n)

noncomputable def phi (n : ℕ) : E n → ℂ := phiS n

lemma phi_eq (n : ℕ) (y : E n) : phi n y = ∫ v, (𝐞 ⟪v, y⟫ : ℂ) * PhiC n v := by
  rw [phi, phiS, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  rfl

lemma phi_integrable (n : ℕ) : Integrable (phi n) := (phiS n).integrable

lemma phi_moment_integrable (n : ℕ) : Integrable (fun u : E n => ‖u‖ * ‖phi n u‖) := by
  simpa [phi] using (phiS n).integrable_pow_mul volume 1

lemma phi_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (phi n) := (phiS n).smooth ⊤

lemma Phi_integrable (n : ℕ) : Integrable (Phi n) := (bump n).integrable_normed

/-- `φ_c(x) = φ((x - c)/R)`. -/
noncomputable def phiLoc (n : ℕ) (R : ℝ) (c : E n) (x : E n) : ℂ := phi n (R⁻¹ • (x - c))

end TaoBR.Tao49.PartW2
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise
namespace TaoBR.Tao49.PartW2
variable {n : ℕ} {R : ℝ} {c : E n}
lemma K_support (hR : 0 < R) {v : E n} (h : Kker n R c v ≠ 0) : ‖v‖ < 1 / (16 * R) := by
  have h1 : PhiC n (R • v) ≠ 0 := by
    intro h0; apply h; simp only [Kker, h0, mul_zero, zero_mul]
  have h2 : Phi n (R • v) ≠ 0 := by simpa [PhiC] using h1
  have h3 := Phi_support n h2
  rw [norm_smul, Real.norm_of_nonneg hR.le] at h3
  rw [lt_div_iff₀ (by positivity)]; linarith

lemma K_norm_le (hR : 0 < R) (v : E n) : ‖Kker n R c v‖ ≤ R ^ n * MPhi n := by
  simp only [Kker, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Phi_nonneg n _)]
  exact mul_le_mul_of_nonneg_left (Phi_le n _) (by positivity)

lemma K_continuous : Continuous (Kker n R c) := by
  have h1 : Continuous (PhiC n) := (PhiC_contDiff n).continuous
  have h2 : Continuous (fun v : E n => (𝐞 (-⟪v, c⟫) : ℂ)) :=
    (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const).neg).subtype_val
  have h3 : Continuous (fun v : E n => PhiC n (R • v)) := h1.comp (continuous_const_smul R)
  exact (continuous_const.mul h3).mul h2

lemma K_integrable (hR : 0 < R) : Integrable (Kker n R c) := by
  refine K_continuous.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E n) (1 / (16 * R))) (fun v hv => ?_)
  by_contra h
  exact hv (mem_closedBall_zero_iff.2 (K_support hR h).le)

lemma fourierInv_K (hR : 0 < R) : 𝓕⁻ (Kker n R c) = phiLoc n R c := by
  funext y
  rw [Real.fourierInv_eq, phiLoc, phi_eq]
  have hcv := MeasureTheory.Measure.integral_comp_smul (volume : Measure (E n))
    (fun u : E n => (𝐞 ⟪u, R⁻¹ • (y - c)⟫ : ℂ) * PhiC n u) R
  rw [finrank_euclideanSpace_fin] at hcv
  have e1 : ∀ v : E n, 𝐞 ⟪v, y⟫ • Kker n R c v =
      ((R ^ n : ℝ) : ℂ) * ((𝐞 ⟪R • v, R⁻¹ • (y - c)⟫ : ℂ) * PhiC n (R • v)) := by
    intro v
    rw [Circle.smul_def, Kker, smul_eq_mul]
    have : ⟪R • v, R⁻¹ • (y - c)⟫ = ⟪v, y⟫ + -⟪v, c⟫ := by
      rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hR.ne',
        one_mul, inner_sub_right]; ring
    rw [this, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  simp_rw [e1]
  rw [integral_const_mul, hcv, Complex.real_smul, abs_of_pos (by positivity)]
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (by positivity),
    Complex.ofReal_one, one_mul]

lemma phiLoc_integrable (hR : 0 < R) : Integrable (phiLoc n R c) := by
  have h1 : Integrable (fun y : E n => phi n (R⁻¹ • y)) :=
    (phi_integrable n).comp_smul (inv_ne_zero hR.ne')
  have h2 := h1.comp_sub_right c
  exact h2

lemma fourier_phiLoc (hR : 0 < R) : 𝓕 (phiLoc n R c) = Kker n R c := by
  have hF : 𝓕 (Kker n R c) = fun w => phiLoc n R c (-w) := by
    funext w
    rw [← fourierInv_K hR, Real.fourierInv_eq_fourier_neg, neg_neg]
  have hFi : Integrable (𝓕 (Kker n R c)) := by
    rw [hF]
    have := (phiLoc_integrable (c := c) hR).comp_smul (show (-1 : ℝ) ≠ 0 by norm_num)
    simpa using this
  rw [← fourierInv_K hR]
  exact K_continuous.fourier_fourierInv_eq (K_integrable hR) hFi

lemma phiLoc_contDiff : ContDiff ℝ (⊤ : ℕ∞) (phiLoc n R c) := by
  exact (phi_contDiff n).comp (by fun_prop)

lemma e_re (t : ℝ) : ((𝐞 t : ℂ)).re = Real.cos (2 * Real.pi * t) := by
  rw [Real.fourierChar_apply, Complex.exp_ofReal_mul_I_re]

lemma phi_lower (n : ℕ) {y : E n} (hy : ‖y‖ < 2) : 1 / 2 ≤ ‖phi n y‖ := by
  have hint : Integrable (fun v : E n => (𝐞 ⟪v, y⟫ : ℂ) * PhiC n v) := by
    refine ((Phi_integrable n).ofReal (𝕜 := ℂ)).bdd_mul (c := 1) ?_ ?_
    · exact (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).subtype_val
        |>.aestronglyMeasurable
    · exact Eventually.of_forall (fun v => (Circle.norm_coe _).le)
  have hre : (phi n y).re = ∫ v, Real.cos (2 * Real.pi * ⟪v, y⟫) * Phi n v := by
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    rw [phi_eq, ← this]
    congr 1; ext v
    simp only [PhiC, RCLike.re_to_complex, Complex.re_mul_ofReal, e_re]
  have hlow : ∫ v, (1 / 2 : ℝ) * Phi n v ≤ ∫ v, Real.cos (2 * Real.pi * ⟪v, y⟫) * Phi n v := by
    refine integral_mono ((Phi_integrable n).const_mul _) ?_ (fun v => ?_)
    · refine (Phi_integrable n).bdd_mul (c := 1) ?_ ?_
      · exact (Real.continuous_cos.comp (continuous_const.mul
          (continuous_id.inner continuous_const))).aestronglyMeasurable
      · exact Eventually.of_forall (fun v => by simpa using Real.abs_cos_le_one _)
    · by_cases h0 : Phi n v = 0
      · simp [h0]
      · have hv := Phi_support n h0
        refine mul_le_mul_of_nonneg_right ?_ (Phi_nonneg n v)
        have h1 : |⟪v, y⟫| ≤ 1 / 8 := by
          refine (abs_real_inner_le_norm v y).trans ?_
          nlinarith [norm_nonneg v, norm_nonneg y]
        have h2 := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * ⟪v, y⟫)
        have h3 : (2 * Real.pi * ⟪v, y⟫) ^ 2 ≤ 1 := by
          rw [mul_pow]
          have : ⟪v, y⟫ ^ 2 ≤ (1 / 8) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
          have hpi : (2 * Real.pi) ^ 2 ≤ 64 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
          nlinarith [sq_nonneg (2 * Real.pi)]
        linarith
  rw [integral_const_mul, Phi_integral, mul_one] at hlow
  calc (1 / 2 : ℝ) ≤ (phi n y).re := by rw [hre]; exact hlow
    _ ≤ ‖phi n y‖ := Complex.re_le_norm _

lemma phiLoc_lower (hR : 0 < R) {y : E n} (hy : dist y c < 2 * R) :
    1 / 2 ≤ ‖phiLoc n R c y‖ := by
  apply phi_lower
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hR.le, ← dist_eq_norm, inv_mul_lt_iff₀ hR]
  linarith

lemma fourier_mul_phiLoc (hR : 0 < R) (g : E n → ℂ) (hg : Integrable g) (ω : E n) :
    𝓕 (fun y => g y * phiLoc n R c y) ω = ∫ η, Kker n R c (ω - η) * 𝓕 g η := by
  have hK := K_integrable (c := c) hR
  have hphi : ∀ y, phiLoc n R c y = ∫ v, (𝐞 ⟪v, y⟫ : ℂ) * Kker n R c v := by
    intro y; rw [← fourierInv_K hR, Real.fourierInv_eq]; rfl
  rw [Real.fourier_eq]
  have e1 : ∀ y, 𝐞 (-⟪y, ω⟫) • (g y * phiLoc n R c y) =
      ∫ v, Kker n R c v * ((𝐞 (-⟪y, ω - v⟫) : ℂ) * g y) := by
    intro y
    rw [hphi, Circle.smul_def, smul_eq_mul, ← integral_const_mul, ← integral_const_mul]
    congr 1; ext v
    have : -⟪y, ω - v⟫ = -⟪y, ω⟫ + ⟪v, y⟫ := by rw [inner_sub_right, real_inner_comm y v]; ring
    rw [this, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  simp_rw [e1]
  have hint : Integrable (Function.uncurry fun (y v : E n) =>
      Kker n R c v * ((𝐞 (-⟪y, ω - v⟫) : ℂ) * g y)) (volume.prod volume) := by
    have hp : Integrable (fun p : E n × E n => Kker n R c p.2 * g p.1) (volume.prod volume) := by
      have := hg.mul_prod hK
      refine this.congr (Eventually.of_forall (fun p => ?_))
      simp [mul_comm]
    refine hp.mono ?_ (Eventually.of_forall (fun p => ?_))
    · refine (K_continuous.comp continuous_snd).aestronglyMeasurable.mul ?_
      refine AEStronglyMeasurable.mul ?_ (hg.aestronglyMeasurable.comp_fst)
      exact (Real.continuous_fourierChar.comp ((continuous_fst.inner
        (continuous_const.sub continuous_snd)).neg)).subtype_val.aestronglyMeasurable
    · simp [Function.uncurry, norm_mul, Circle.norm_coe]
  rw [integral_integral_swap hint]
  have e2 : ∀ v, ∫ y, Kker n R c v * ((𝐞 (-⟪y, ω - v⟫) : ℂ) * g y) =
      Kker n R c v * 𝓕 g (ω - v) := by
    intro v; rw [integral_const_mul, Real.fourier_eq]; rfl
  simp_rw [e2]
  have := integral_sub_left_eq_self (fun v => Kker n R c v * 𝓕 g (ω - v)) (volume : Measure (E n)) ω
  rw [← this]
  simp only [sub_sub_cancel]

end TaoBR.Tao49.PartW2
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise
namespace TaoBR.Tao49.PartW2
noncomputable def truncHi {ι X : Type*} (G : ι → X → ℂ) (t : ℝ) : ι → X → ℂ :=
  fun i x => if t < ‖G i x‖ then G i x else 0

noncomputable def truncLo {ι X : Type*} (G : ι → X → ℂ) (t : ℝ) : ι → X → ℂ :=
  fun i x => if t < ‖G i x‖ then 0 else G i x

lemma truncHi_add_truncLo {ι X : Type*} (G : ι → X → ℂ) (t : ℝ) :
    truncHi G t + truncLo G t = G := by
  funext i x
  simp only [truncHi, truncLo, Pi.add_apply]
  split_ifs <;> simp

lemma enorm_truncHi {ι X : Type*} (G : ι → X → ℂ) (t : ℝ) (i : ι) (x : X) :
    ‖truncHi G t i x‖ₑ = if t < ‖G i x‖ then ENNReal.ofReal ‖G i x‖ else 0 := by
  simp only [truncHi]; split_ifs <;> simp

lemma enorm_truncLo_sq {ι X : Type*} (G : ι → X → ℂ) (t : ℝ) (i : ι) (x : X) :
    ‖truncLo G t i x‖ₑ ^ (2 : ℝ) = if t < ‖G i x‖ then 0 else ENNReal.ofReal (‖G i x‖ ^ 2) := by
  simp only [truncLo]; split_ifs
  · simp
  · rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    norm_num

/-- `∫_0^s t^(q-2) dt = s^(q-1)/(q-1)`. -/
lemma lint_low {q : ℝ} (hq1 : 1 < q) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ t in Ioo 0 s, ENNReal.ofReal (t ^ (q - 2)) = ENNReal.ofReal (s ^ (q - 1) / (q - 1)) := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (q - 2)) volume 0 s :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hio : IntegrableOn (fun t : ℝ => t ^ (q - 2)) (Ioo 0 s) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hs).1 hint).mono_set Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hio]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs,
      integral_rpow (Or.inl (by linarith))]
    rw [show q - 2 + 1 = q - 1 by ring, Real.zero_rpow (by linarith)]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _

/-- `∫_s^∞ t^(q-3) dt = s^(q-2)/(2-q)`. -/
lemma lint_high {q : ℝ} (hq2 : q < 2) {s : ℝ} (hs : 0 < s) :
    ∫⁻ t in Ioi s, ENNReal.ofReal (t ^ (q - 3)) = ENNReal.ofReal (s ^ (q - 2) / (2 - q)) := by
  have hio : IntegrableOn (fun t : ℝ => t ^ (q - 3)) (Ioi s) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hs
  rw [← ofReal_integral_eq_lintegral_ofReal hio]
  · congr 1
    rw [integral_Ioi_rpow_of_lt (by linarith) hs, show q - 3 + 1 = q - 2 by ring]
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hs.trans ht).le _

/-- The per-point one-dimensional computation. -/
lemma lint_point {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ t in Ioi 0, (ENNReal.ofReal (2 / t) * (if t < s then ENNReal.ofReal s else 0) +
        ENNReal.ofReal (4 / t ^ 2) * (if t < s then 0 else ENNReal.ofReal (s ^ 2))) *
        ENNReal.ofReal (t ^ (q - 1)) ≤
      ENNReal.ofReal ((2 / (q - 1) + 4 / (2 - q)) * s ^ q) := by
  rcases hs.eq_or_lt with hs0 | hs0
  · subst hs0
    have : ∀ t ∈ Ioi (0 : ℝ), (ENNReal.ofReal (2 / t) * (if t < 0 then ENNReal.ofReal 0 else 0) +
        ENNReal.ofReal (4 / t ^ 2) * (if t < 0 then 0 else ENNReal.ofReal (0 ^ 2))) *
        ENNReal.ofReal (t ^ (q - 1)) = 0 := by
      intro t ht; simp
    rw [setLIntegral_congr_fun measurableSet_Ioi this]; simp
  have e1 : ∀ t ∈ Ioi (0 : ℝ), (ENNReal.ofReal (2 / t) * (if t < s then ENNReal.ofReal s else 0) +
        ENNReal.ofReal (4 / t ^ 2) * (if t < s then 0 else ENNReal.ofReal (s ^ 2))) *
        ENNReal.ofReal (t ^ (q - 1)) =
      (Iio s).indicator (fun t => ENNReal.ofReal (2 * s) * ENNReal.ofReal (t ^ (q - 2))) t +
      (Ici s).indicator (fun t => ENNReal.ofReal (4 * s ^ 2) * ENNReal.ofReal (t ^ (q - 3))) t := by
    intro t ht
    have ht : 0 < t := ht
    have r1 : t ^ (q - 1) = t ^ (q - 2) * t := by
      rw [← Real.rpow_add_one ht.ne']; ring_nf
    have r2 : t ^ (q - 1) = t ^ (q - 3) * t ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add ht]; ring_nf
    by_cases h : t < s
    · have h' : t ∉ Ici s := by simpa using h
      rw [if_pos h, if_pos h, indicator_of_mem (show t ∈ Iio s from h), indicator_of_notMem h',
        mul_zero, add_zero, add_zero, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1; rw [r1]; field_simp
    · have h' : t ∈ Ici s := by simpa using h
      rw [if_neg h, if_neg h, indicator_of_notMem (show t ∉ Iio s from h), indicator_of_mem h',
        mul_zero, zero_add, zero_add, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1; rw [r2]; field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi e1]
  rw [lintegral_add_left]
  swap
  · exact Measurable.indicator (by fun_prop) measurableSet_Iio
  rw [lintegral_indicator measurableSet_Iio, lintegral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Iio, Measure.restrict_restrict measurableSet_Ici,
    lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop)]
  have i1 : Iio s ∩ Ioi 0 = Ioo 0 s := by ext; simp [and_comm]
  have i2 : Ici s ∩ Ioi (0 : ℝ) = Ici s := inter_eq_left.2 (fun t ht => hs0.trans_le ht)
  rw [i1, i2, setLIntegral_congr Ioi_ae_eq_Ici.symm, lint_low hq1 hs, lint_high hq2 hs0,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply le_of_eq; congr 1
  have a1 : s * s ^ (q - 1) = s ^ q := by
    rw [← Real.rpow_one_add' hs0.le (by linarith)]; ring_nf
  have a2 : s ^ 2 * s ^ (q - 2) = s ^ q := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hs0]; ring_nf
  have hq1' : q - 1 ≠ 0 := by linarith
  have hq2' : 2 - q ≠ 0 := by linarith
  calc 2 * s * (s ^ (q - 1) / (q - 1)) + 4 * s ^ 2 * (s ^ (q - 2) / (2 - q))
      = 2 * (s * s ^ (q - 1)) / (q - 1) + 4 * (s ^ 2 * s ^ (q - 2)) / (2 - q) := by ring
    _ = _ := by rw [a1, a2]; ring

end TaoBR.Tao49.PartW2
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise
namespace TaoBR.Tao49.PartW2
variable {ι : Type*} [Fintype ι] {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (P : (ι → X → ℂ) → Prop)
    (T : (ι → X → ℂ) → Y → ℂ) (A : ℝ≥0∞)
omit [SFinite μ] [SFinite ν] in
include P in
lemma marc_step
    (hPhi : ∀ G t, P G → P (truncHi G t)) (hPlo : ∀ G t, P G → P (truncLo G t))
    (hlin : ∀ G G', P G → P G' → T (G + G') = T G + T G')
    (hmeasT : ∀ G, P G → Measurable (T G))
    (h1 : ∀ G, P G → ∫⁻ y, ‖T G y‖ₑ ∂ν ≤ A * ∑ i, ∫⁻ x, ‖G i x‖ₑ ∂μ)
    (h2 : ∀ G, P G → ∫⁻ y, ‖T G y‖ₑ ^ (2 : ℝ) ∂ν ≤ A * ∑ i, ∫⁻ x, ‖G i x‖ₑ ^ (2 : ℝ) ∂μ)
    (G : ι → X → ℂ) (hG : P G) (t : ℝ) (ht : 0 < t) :
    ν {y | t < ‖T G y‖} ≤
      A * (ENNReal.ofReal (2 / t) * (∑ i, ∫⁻ x, ‖truncHi G t i x‖ₑ ∂μ) +
        ENNReal.ofReal (4 / t ^ 2) * (∑ i, ∫⁻ x, ‖truncLo G t i x‖ₑ ^ (2 : ℝ) ∂μ)) := by
  have hsplit : T G = T (truncHi G t) + T (truncLo G t) := by
    rw [← hlin _ _ (hPhi G t hG) (hPlo G t hG), truncHi_add_truncLo]
  have hsub : {y | t < ‖T G y‖} ⊆ {y | t / 2 ≤ ‖T (truncHi G t) y‖} ∪
      {y | t / 2 ≤ ‖T (truncLo G t) y‖} := by
    intro y hy
    simp only [mem_setOf_eq, mem_union] at hy ⊢
    by_contra hc
    push Not at hc
    rw [hsplit, Pi.add_apply] at hy
    linarith [norm_add_le (T (truncHi G t) y) (T (truncLo G t) y)]
  have c1 : ν {y | t / 2 ≤ ‖T (truncHi G t) y‖} ≤ ENNReal.ofReal (2 / t) * (A * (∑ i, ∫⁻ x, ‖truncHi G t i x‖ₑ ∂μ)) := by
    have hm := (hmeasT _ (hPhi G t hG)).enorm.aemeasurable (μ := ν)
    have := mul_meas_ge_le_lintegral₀ hm (ENNReal.ofReal (t / 2))
    have hset : {y | ENNReal.ofReal (t / 2) ≤ ‖T (truncHi G t) y‖ₑ} =
        {y | t / 2 ≤ ‖T (truncHi G t) y‖} := by
      ext y; simp only [mem_setOf_eq, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)
    rw [hset] at this
    have hpos : ENNReal.ofReal (t / 2) ≠ 0 := by simpa using ht
    have e2 : ENNReal.ofReal (2 / t) = (ENNReal.ofReal (t / 2))⁻¹ := by
      rw [← ENNReal.ofReal_inv_of_pos (by positivity)]; congr 1; field_simp
    rw [e2, ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hpos)
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact this.trans (h1 _ (hPhi G t hG))
  have c2 : ν {y | t / 2 ≤ ‖T (truncLo G t) y‖} ≤ ENNReal.ofReal (4 / t ^ 2) * (A * (∑ i, ∫⁻ x, ‖truncLo G t i x‖ₑ ^ (2 : ℝ) ∂μ)) := by
    have hm := ((hmeasT _ (hPlo G t hG)).enorm.pow_const (2 : ℝ)).aemeasurable (μ := ν)
    have := mul_meas_ge_le_lintegral₀ hm (ENNReal.ofReal ((t / 2) ^ 2))
    have hset : {y | ENNReal.ofReal ((t / 2) ^ 2) ≤ ‖T (truncLo G t) y‖ₑ ^ (2 : ℝ)} =
        {y | t / 2 ≤ ‖T (truncLo G t) y‖} := by
      ext y; simp only [mem_setOf_eq, ← ofReal_norm]
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        ENNReal.ofReal_le_ofReal_iff (by positivity), Real.rpow_two]
      exact pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero
    rw [hset] at this
    have hpos : ENNReal.ofReal ((t / 2) ^ 2) ≠ 0 := by simpa using ht.ne'
    have e2 : ENNReal.ofReal (4 / t ^ 2) = (ENNReal.ofReal ((t / 2) ^ 2))⁻¹ := by
      rw [← ENNReal.ofReal_inv_of_pos (by positivity)]; congr 1; field_simp; ring
    rw [e2, ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hpos)
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact this.trans (h2 _ (hPlo G t hG))
  calc ν {y | t < ‖T G y‖} ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add c1 c2
    _ = _ := by ring

/-- The integrand after the layer-cake step. -/
noncomputable def marcF (G : ι → X → ℂ) (q : ℝ) (i : ι) (t : ℝ) (x : X) : ℝ≥0∞ :=
  (ENNReal.ofReal (2 / t) * (if t < ‖G i x‖ then ENNReal.ofReal ‖G i x‖ else 0) +
    ENNReal.ofReal (4 / t ^ 2) * (if t < ‖G i x‖ then 0 else ENNReal.ofReal (‖G i x‖ ^ 2))) *
    ENNReal.ofReal (t ^ (q - 1))

omit [Fintype ι] in
lemma marcF_meas (G : ι → X → ℂ) (hG : ∀ i, Measurable (G i)) (q : ℝ) (i : ι) :
    Measurable (Function.uncurry (marcF G q i)) := by
  have hg : Measurable (fun p : ℝ × X => ‖G i p.2‖) := (hG i).norm.comp measurable_snd
  have hs : MeasurableSet {p : ℝ × X | p.1 < ‖G i p.2‖} := measurableSet_lt measurable_fst hg
  refine Measurable.mul (Measurable.add ?_ ?_) ?_
  · exact (by fun_prop : Measurable fun p : ℝ × X => ENNReal.ofReal (2 / p.1)).mul
      (Measurable.ite hs hg.ennreal_ofReal measurable_const)
  · exact (by fun_prop : Measurable fun p : ℝ × X => ENNReal.ofReal (4 / p.1 ^ 2)).mul
      (Measurable.ite hs measurable_const (hg.pow_const 2).ennreal_ofReal)
  · exact (measurable_fst.pow_const _).ennreal_ofReal

omit [SFinite μ] in
lemma marcF_sum (G : ι → X → ℂ) (hG : ∀ i, Measurable (G i)) (q t : ℝ) :
    ∑ i, ∫⁻ x, marcF G q i t x ∂μ =
      (ENNReal.ofReal (2 / t) * (∑ i, ∫⁻ x, ‖truncHi G t i x‖ₑ ∂μ) +
        ENNReal.ofReal (4 / t ^ 2) * (∑ i, ∫⁻ x, ‖truncLo G t i x‖ₑ ^ (2 : ℝ) ∂μ)) *
        ENNReal.ofReal (t ^ (q - 1)) := by
  simp only [enorm_truncHi, enorm_truncLo_sq, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hs : MeasurableSet {x | t < ‖G i x‖} := measurableSet_lt measurable_const (hG i).norm
  have m1 : Measurable (fun x => if t < ‖G i x‖ then ENNReal.ofReal ‖G i x‖ else 0) :=
    Measurable.ite hs (hG i).norm.ennreal_ofReal measurable_const
  have m2 : Measurable (fun x => if t < ‖G i x‖ then 0 else ENNReal.ofReal (‖G i x‖ ^ 2)) :=
    Measurable.ite hs measurable_const ((hG i).norm.pow_const 2).ennreal_ofReal
  unfold marcF
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [lintegral_add_left (m1.const_mul _), lintegral_const_mul _ m1,
    lintegral_const_mul _ m2]

omit [Fintype ι] [MeasurableSpace X] in
lemma marcF_point {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) (G : ι → X → ℂ) (i : ι) (x : X) :
    ∫⁻ t in Ioi 0, marcF G q i t x ≤
      ENNReal.ofReal (2 / (q - 1) + 4 / (2 - q)) * ‖G i x‖ₑ ^ q := by
  refine (lint_point hq1 hq2 (norm_nonneg (G i x))).trans (le_of_eq ?_)
  have : 0 < q - 1 := by linarith
  have : 0 < 2 - q := by linarith
  rw [ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith)]

include P in
/-- The interpolation step. -/
lemma marc
    (hPhi : ∀ G t, P G → P (truncHi G t)) (hPlo : ∀ G t, P G → P (truncLo G t))
    (hlin : ∀ G G', P G → P G' → T (G + G') = T G + T G')
    (hmeasT : ∀ G, P G → Measurable (T G))
    (hmeasG : ∀ G, P G → ∀ i, Measurable (G i))
    (h1 : ∀ G, P G → ∫⁻ y, ‖T G y‖ₑ ∂ν ≤ A * ∑ i, ∫⁻ x, ‖G i x‖ₑ ∂μ)
    (h2 : ∀ G, P G → ∫⁻ y, ‖T G y‖ₑ ^ (2 : ℝ) ∂ν ≤ A * ∑ i, ∫⁻ x, ‖G i x‖ₑ ^ (2 : ℝ) ∂μ)
    {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) (G : ι → X → ℂ) (hG : P G) :
    ∫⁻ y, ‖T G y‖ₑ ^ q ∂ν ≤
      ENNReal.ofReal (q * (2 / (q - 1) + 4 / (2 - q))) * A * ∑ i, ∫⁻ x, ‖G i x‖ₑ ^ q ∂μ := by
  have hq0 : 0 < q := by linarith
  have hlc := lintegral_rpow_eq_lintegral_meas_lt_mul ν (f := fun y => ‖T G y‖)
    (Eventually.of_forall (fun y => norm_nonneg _)) (hmeasT G hG).norm.aemeasurable hq0
  have e0 : ∫⁻ y, ‖T G y‖ₑ ^ q ∂ν = ∫⁻ y, ENNReal.ofReal (‖T G y‖ ^ q) ∂ν := by
    congr 1; ext y
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le]
  rw [e0, hlc]
  have hFm := marcF_meas G (hmeasG G hG) q
  have key : ∀ t ∈ Ioi (0 : ℝ), ν {y | t < ‖T G y‖} * ENNReal.ofReal (t ^ (q - 1)) ≤
      A * ∑ i, ∫⁻ x, marcF G q i t x ∂μ := by
    intro t ht
    rw [marcF_sum μ G (hmeasG G hG), ← mul_assoc]
    gcongr
    exact marc_step μ ν P T A hPhi hPlo hlin hmeasT h1 h2 G hG t ht
  calc ENNReal.ofReal q * ∫⁻ t in Ioi 0, ν {y | t < ‖T G y‖} * ENNReal.ofReal (t ^ (q - 1))
      ≤ ENNReal.ofReal q * ∫⁻ t in Ioi 0, A * ∑ i, ∫⁻ x, marcF G q i t x ∂μ := by
        gcongr 1
        exact setLIntegral_mono' measurableSet_Ioi key
    _ = ENNReal.ofReal q * (A * ∑ i, ∫⁻ x, (∫⁻ t in Ioi 0, marcF G q i t x) ∂μ) := by
        congr 1
        have hmi : ∀ i ∈ (Finset.univ : Finset ι),
            Measurable (fun t => ∫⁻ x, marcF G q i t x ∂μ) :=
          fun i _ => (hFm i).lintegral_prod_right'
        have hm : Measurable (fun t => ∑ i, ∫⁻ x, marcF G q i t x ∂μ) :=
          Finset.measurable_sum _ hmi
        rw [lintegral_const_mul _ hm]
        congr 1
        rw [lintegral_finsetSum _ hmi]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact lintegral_lintegral_swap (hFm i).aemeasurable
    _ ≤ ENNReal.ofReal q * (A * ∑ i, ∫⁻ x,
          ENNReal.ofReal (2 / (q - 1) + 4 / (2 - q)) * ‖G i x‖ₑ ^ q ∂μ) := by
        gcongr with i _ x
        exact marcF_point hq1 hq2 G i x
    _ = _ := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [← Finset.mul_sum, ENNReal.ofReal_mul hq0.le]
        ring

end TaoBR.Tao49.PartW2
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise
namespace TaoBR.Tao49.PartW2
lemma sparse_far {n : ℕ} {R : ℝ} (hR : 1 ≤ R) {N : ℕ} {x : Fin N → E n}
    (hx : IsSparse ((3 * n + 3 : ℕ) : ℝ) R x) {i j : Fin N} (hij : i ≠ j) :
    8 * R ≤ dist (x i) (x j) := by
  have h := hx i j hij
  rw [Real.rpow_natCast, Real.rpow_natCast] at h
  have hN : (2 : ℝ) ≤ N := by
    have : 2 ≤ N := by
      by_contra hc
      push Not at hc
      interval_cases N
      · exact i.elim0
      · exact hij (Subsingleton.elim _ _)
    exact_mod_cast this
  have h1 : R ≤ R ^ (3 * n + 3) := le_self_pow₀ hR (by omega)
  have h2 : (8 : ℝ) ≤ (N : ℝ) ^ (3 * n + 3) := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (3 * n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hN _
  have : 8 * R ≤ R ^ (3 * n + 3) * (N : ℝ) ^ (3 * n + 3) := by nlinarith
  linarith

/-- The pieces `g_i = f / φ_i` near `x_i`. -/
noncomputable def gfun (n : ℕ) (R : ℝ) (c : E n) (f : E n → ℂ) (y : E n) : ℂ :=
  if dist y c < 2 * R then f y / phiLoc n R c y else 0

lemma decomp (n : ℕ) (hn : 2 ≤ n) {R : ℝ} (hR : 1 ≤ R) {N : ℕ} (x : Fin N → E n)
    (hx : IsSparse ((3 * n + 3 : ℕ) : ℝ) R x) (f : 𝓢(E n, ℂ))
    (hf : tsupport f ⊆ ⋃ i, closedBall (x i) R) {q : ℝ} (hq : 0 < q) :
    ∃ g : Fin N → 𝓢(E n, ℂ), (∀ i, tsupport (g i) ⊆ closedBall (x i) R) ∧
      (∀ y, f y = ∑ i, g i y * phiLoc n R (x i) y) ∧
      ∑ i, ∫⁻ y, ‖g i y‖ₑ ^ q ≤ (2 : ℝ≥0∞) ^ q * ∫⁻ y, ‖f y‖ₑ ^ q := by
  have hR0 : 0 < R := by linarith
  -- f vanishes off the balls
  have hf0 : ∀ y, (∀ i, R < dist y (x i)) → f y = 0 := by
    intro y hy
    by_contra h
    have : y ∈ ⋃ i, closedBall (x i) R := hf (subset_tsupport _ h)
    obtain ⟨i, hi⟩ := mem_iUnion.1 this
    exact absurd (mem_closedBall.1 hi) (not_le.2 (hy i))
  -- uniqueness of the nearby centre
  have huniq : ∀ y i j, dist y (x i) < 2 * R → i ≠ j → 2 * R ≤ dist y (x j) := by
    intro y i j hi hij
    have := sparse_far hR hx hij
    have := dist_triangle (x i) y (x j)
    rw [dist_comm (x i) y] at this
    linarith
  have hzero : ∀ i y, R < dist y (x i) → gfun n R (x i) f y = 0 := by
    intro i y hy
    unfold gfun
    split_ifs with h
    · rw [hf0 y (fun j => ?_), zero_div]
      by_cases hij : i = j
      · subst hij; exact hy
      · linarith [huniq y i j h hij]
    · rfl
  have hsupp : ∀ i, tsupport (gfun n R (x i) f) ⊆ closedBall (x i) R := by
    intro i
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    by_contra h
    exact hy (hzero i y (not_le.1 (fun h' => h (mem_closedBall.2 h'))))
  have hcs : ∀ i, HasCompactSupport (gfun n R (x i) f) := fun i =>
    (isCompact_closedBall (x i) R).of_isClosed_subset (isClosed_tsupport _) (hsupp i)
  have hcd : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (gfun n R (x i) f) := by
    intro i
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : dist y (x i) < 2 * R
    · have hev : gfun n R (x i) f =ᶠ[𝓝 y] fun z => f z / phiLoc n R (x i) z := by
        filter_upwards [isOpen_lt (continuous_id.dist continuous_const) continuous_const
          |>.mem_nhds hy] with z hz
        simp only [gfun, if_pos (show dist z (x i) < 2 * R from hz)]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      have hne : phiLoc n R (x i) y ≠ 0 := by
        intro h0; have := phiLoc_lower (c := x i) hR0 hy; rw [h0, norm_zero] at this
        norm_num at this
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (phiLoc n R (x i))⁻¹ y :=
        ContDiffAt.inv (phiLoc_contDiff.contDiffAt) hne
      have h2 := ((f.smooth ⊤).contDiffAt (x := y)).mul h1
      refine h2.congr_of_eventuallyEq (Eventually.of_forall (fun z => ?_))
      simp [div_eq_mul_inv]
    · have hy' : R < dist y (x i) := by linarith
      have hev : gfun n R (x i) f =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [isOpen_lt continuous_const (continuous_id.dist continuous_const)
          |>.mem_nhds hy'] with z hz
        exact hzero i z hz
      exact contDiffAt_const.congr_of_eventuallyEq hev
  refine ⟨fun i => (hcs i).toSchwartzMap (hcd i), fun i => hsupp i, ?_, ?_⟩
  · intro y
    show f y = ∑ i, gfun n R (x i) f y * phiLoc n R (x i) y
    by_cases h : ∃ i, dist y (x i) < 2 * R
    · obtain ⟨i, hi⟩ := h
      rw [Finset.sum_eq_single i]
      · have hne : phiLoc n R (x i) y ≠ 0 := by
          intro h0; have := phiLoc_lower (c := x i) hR0 hi; rw [h0, norm_zero] at this
          norm_num at this
        simp only [gfun, if_pos hi]
        field_simp
      · intro j _ hji
        have := huniq y i j hi (Ne.symm hji)
        simp only [gfun, if_neg (not_lt.2 this), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h
    · push Not at h
      rw [hf0 y (fun i => by linarith [h i])]
      symm
      refine Finset.sum_eq_zero (fun i _ => ?_)
      simp only [gfun, if_neg (not_lt.2 (h i)), zero_mul]
  · -- pointwise bound
    have hpt : ∀ y, ∑ i, ‖gfun n R (x i) f y‖ₑ ^ q ≤ (2 : ℝ≥0∞) ^ q * ‖f y‖ₑ ^ q := by
      intro y
      by_cases h : ∃ i, dist y (x i) < 2 * R
      · obtain ⟨i, hi⟩ := h
        rw [Finset.sum_eq_single i]
        · have hl := phiLoc_lower (c := x i) hR0 hi
          have hb : ‖gfun n R (x i) f y‖ ≤ 2 * ‖f y‖ := by
            simp only [gfun, if_pos hi, norm_div]
            rw [div_le_iff₀ (by linarith)]
            nlinarith [norm_nonneg (f y)]
          rw [← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
          refine ENNReal.rpow_le_rpow ?_ hq.le
          rw [← ofReal_norm, ← ofReal_norm]
          calc ENNReal.ofReal ‖gfun n R (x i) f y‖ ≤ ENNReal.ofReal (2 * ‖f y‖) :=
                ENNReal.ofReal_le_ofReal hb
            _ = 2 * ENNReal.ofReal ‖f y‖ := by
                rw [ENNReal.ofReal_mul (by norm_num)]; simp
        · intro j _ hji
          have := huniq y i j hi (Ne.symm hji)
          simp only [gfun, if_neg (not_lt.2 this), enorm_zero, ENNReal.zero_rpow_of_pos hq]
        · intro h; exact absurd (Finset.mem_univ i) h
      · push Not at h
        rw [Finset.sum_eq_zero (fun i _ => by
          simp only [gfun, if_neg (not_lt.2 (h i)), enorm_zero, ENNReal.zero_rpow_of_pos hq])]
        exact bot_le
    have hmeas : ∀ i, Measurable (fun y => ‖gfun n R (x i) f y‖ₑ ^ q) := fun i =>
      ((hcd i).continuous.measurable.enorm).pow_const q
    show ∑ i, ∫⁻ y, ‖gfun n R (x i) f y‖ₑ ^ q ≤ _
    rw [← lintegral_finsetSum _ (fun i _ => hmeas i), ← lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg hq.le (by simp))]
    exact lintegral_mono hpt

end TaoBR.Tao49.PartW2
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise
namespace TaoBR.Tao49.PartW2
variable {n : ℕ} {N : ℕ} {R : ℝ} {x : Fin N → E n}
/-! ## The operator `T` against a measure on `E n` -/
lemma Top_add (hR : 0 < R) (G G' : Fin N → E n → ℂ) (hG : ∀ i, Integrable (G i))
    (hG' : ∀ i, Integrable (G' i)) : Top R x (G + G') = Top R x G + Top R x G' := by
  funext ω
  simp only [Top, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hb : ∀ (H : E n → ℂ), Integrable H →
      Integrable (fun η => Kker n R (x i) (ω - η) * H η) := by
    intro H hH
    refine hH.bdd_mul (c := R ^ n * MPhi n) ?_ (Eventually.of_forall (fun η => K_norm_le hR _))
    exact (K_continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  rw [← integral_add (hb _ (hG i)) (hb _ (hG' i))]
  congr 1; ext η; ring

lemma Top_meas (G : Fin N → E n → ℂ) (hG : ∀ i, Measurable (G i)) :
    Measurable (Top R x G) := by
  unfold Top
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine StronglyMeasurable.measurable ?_
  refine StronglyMeasurable.integral_prod_right (f := fun (ω : E n) (η : E n) =>
    Kker n R (x i) (ω - η) * G i η) ?_
  refine Measurable.stronglyMeasurable ?_
  exact (K_continuous.measurable.comp (measurable_fst.sub measurable_snd)).mul
    ((hG i).comp measurable_snd)

lemma K_lintegral (hR : 0 < R) (c : E n) : ∫⁻ v, ‖Kker n R c v‖ₑ = 1 := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (K_integrable hR)]
  have e : ∀ v : E n, ‖Kker n R c v‖ = R ^ n * Phi n (R • v) := by
    intro v
    simp only [Kker, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one]
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Phi_nonneg n _)]
  simp_rw [e]
  rw [integral_const_mul, Measure.integral_comp_smul, finrank_euclideanSpace_fin, Phi_integral,
    smul_eq_mul, mul_one, abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity),
    ENNReal.ofReal_one]

lemma K_enorm_center (c v : E n) : ‖Kker n R c v‖ₑ = ‖Kker n R 0 v‖ₑ := by
  simp only [Kker, enorm_mul]
  congr 1
  rw [← ofReal_norm, ← ofReal_norm, Circle.norm_coe, Circle.norm_coe]

lemma Wt_meas (μ : Measure (E n)) [SFinite μ] : Measurable (Wt μ R) := by
  unfold Wt
  exact (K_continuous.measurable.comp (measurable_fst.sub measurable_snd)).enorm.lintegral_prod_left'

/-- The `L¹` bound against the smoothed weight (Tonelli). -/
lemma Top_L1 {μ : Measure (E n)} [SFinite μ]
    (G : Fin N → E n → ℂ) (hG : ∀ i, Measurable (G i)) :
    ∫⁻ ω, ‖Top R x G ω‖ₑ ∂μ ≤ ∑ i, ∫⁻ η, ‖G i η‖ₑ * Wt μ R η := by
  have hpt : ∀ ω, ‖Top R x G ω‖ₑ ≤ ∑ i, ∫⁻ η, ‖Kker n R (x i) (ω - η)‖ₑ * ‖G i η‖ₑ := by
    intro ω
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    simp_rw [enorm_mul]
  have hm : ∀ i, Measurable (Function.uncurry fun (ω : E n) (η : E n) =>
      ‖Kker n R (x i) (ω - η)‖ₑ * ‖G i η‖ₑ) := by
    intro i
    exact (K_continuous.measurable.comp (measurable_fst.sub measurable_snd)).enorm.mul
      ((hG i).comp measurable_snd).enorm
  refine (lintegral_mono hpt).trans ?_
  have hmi : ∀ i ∈ (Finset.univ : Finset (Fin N)), Measurable (fun ω : E n =>
      ∫⁻ η, ‖Kker n R (x i) (ω - η)‖ₑ * ‖G i η‖ₑ) := fun i _ => (hm i).lintegral_prod_right'
  rw [lintegral_finsetSum _ hmi]
  refine Finset.sum_le_sum (fun i _ => le_of_eq ?_)
  rw [lintegral_lintegral_swap (hm i).aemeasurable]
  refine lintegral_congr (fun η => ?_)
  rw [lintegral_mul_const' _ _ enorm_ne_top, mul_comm, Wt]
  simp_rw [K_enorm_center (x i)]

end TaoBR.Tao49.PartW2
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise
namespace TaoBR.Tao49.PartW2
variable {n : ℕ} {R : ℝ} {N : ℕ}
/-! ## The input class -/
/-- The class of inputs: measurable, bounded, supported in `B(0, 2)`. -/
def PG {N : ℕ} (G : Fin N → E n → ℂ) : Prop :=
  ∀ i, Measurable (G i) ∧ (∃ B : ℝ, ∀ η, ‖G i η‖ ≤ B) ∧ ∀ η ∉ closedBall (0 : E n) 2, G i η = 0

lemma PG_eq_indicator {G : Fin N → E n → ℂ} (hG : PG G) (i : Fin N) :
    G i = (closedBall (0 : E n) 2).indicator (G i) := by
  funext η
  by_cases h : η ∈ closedBall (0 : E n) 2
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h, (hG i).2.2 η h]

lemma PG_integrable {G : Fin N → E n → ℂ} (hG : PG G) (i : Fin N) : Integrable (G i) := by
  obtain ⟨B, hB⟩ := (hG i).2.1
  rw [PG_eq_indicator hG i, integrable_indicator_iff measurableSet_closedBall]
  exact Measure.integrableOn_of_bounded (M := B) measure_closedBall_lt_top.ne
    (hG i).1.aestronglyMeasurable (Eventually.of_forall hB)

lemma PG_truncHi {G : Fin N → E n → ℂ} (hG : PG G) (t : ℝ) : PG (truncHi G t) := by
  intro i
  obtain ⟨hm, ⟨B, hB⟩, hs⟩ := hG i
  refine ⟨Measurable.ite (measurableSet_lt measurable_const hm.norm) hm measurable_const,
    ⟨max B 0, fun η => ?_⟩, fun η hη => ?_⟩
  · simp only [truncHi]; split_ifs
    · exact (hB η).trans (le_max_left _ _)
    · simp
  · simp only [truncHi, hs η hη]; simp

lemma PG_truncLo {G : Fin N → E n → ℂ} (hG : PG G) (t : ℝ) : PG (truncLo G t) := by
  intro i
  obtain ⟨hm, ⟨B, hB⟩, hs⟩ := hG i
  refine ⟨Measurable.ite (measurableSet_lt measurable_const hm.norm) measurable_const hm,
    ⟨max B 0, fun η => ?_⟩, fun η hη => ?_⟩
  · simp only [truncLo]; split_ifs
    · simp
    · exact (hB η).trans (le_max_left _ _)
  · simp only [truncLo, hs η hη]; simp

lemma mem_B2_of_K (hR : 1 ≤ R) {c ω η : E n} (hω : ‖ω‖ ≤ 3 / 2)
    (h : Kker n R c (ω - η) ≠ 0) : η ∈ closedBall (0 : E n) 2 := by
  have h1 := K_support (by linarith) h
  have h2 : 1 / (16 * R) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  rw [mem_closedBall_zero_iff]
  have := norm_sub_le ω (ω - η)
  rw [sub_sub_cancel] at this
  linarith

lemma fourier_eq_Top (hR : 1 ≤ R) (x : Fin N → E n) (f : 𝓢(E n, ℂ))
    (g : Fin N → 𝓢(E n, ℂ)) (hgs : ∀ i, tsupport (g i) ⊆ closedBall (x i) R)
    (hfg : ∀ y, f y = ∑ i, g i y * phiLoc n R (x i) y) {ω : E n} (hω : ‖ω‖ ≤ 3 / 2) :
    𝓕 (f : E n → ℂ) ω =
      Top R x (fun i => (closedBall (0 : E n) 2).indicator (𝓕 (g i : E n → ℂ))) ω := by
  have hR0 : 0 < R := by linarith
  have hint : ∀ i, Integrable (fun y => g i y * phiLoc n R (x i) y) := by
    intro i
    have hc : HasCompactSupport (g i : E n → ℂ) :=
      HasCompactSupport.intro (isCompact_closedBall (x i) R)
        (fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hgs i h)))
    exact ((g i).continuous.mul phiLoc_contDiff.continuous).integrable_of_hasCompactSupport
      hc.mul_right
  simp only [Top]
  have hf : (f : E n → ℂ) = fun y => ∑ i, g i y * phiLoc n R (x i) y := funext hfg
  rw [hf, Real.fourier_eq]
  simp_rw [Finset.smul_sum]
  rw [integral_finsetSum _ (fun i _ => (Real.fourierIntegral_convergent_iff _).2 (hint i))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have := fourier_mul_phiLoc (c := x i) hR0 (g i) (g i).integrable ω
  rw [Real.fourier_eq] at this
  rw [this]
  refine integral_congr_ae (Eventually.of_forall (fun η => ?_))
  by_cases hK : Kker n R (x i) (ω - η) = 0
  · simp [hK]
  · simp only
    rw [indicator_of_mem (mem_B2_of_K hR hω hK)]

lemma fourier_continuous (g : 𝓢(E n, ℂ)) : Continuous (𝓕 (g : E n → ℂ)) := by
  rw [← SchwartzMap.fourier_coe]; exact (𝓕 g).continuous

lemma PG_G (g : Fin N → 𝓢(E n, ℂ)) :
    PG (fun i => (closedBall (0 : E n) 2).indicator (𝓕 (g i : E n → ℂ))) := by
  intro i
  refine ⟨(fourier_continuous (g i)).measurable.indicator measurableSet_closedBall,
    ⟨∫ y, ‖g i y‖, fun η => ?_⟩, fun η hη => indicator_of_notMem hη _⟩
  dsimp only
  by_cases h : η ∈ closedBall (0 : E n) 2
  · rw [indicator_of_mem h]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  · rw [indicator_of_notMem h, norm_zero]
    exact integral_nonneg (fun _ => norm_nonneg _)

lemma isSparse_mono {C C' : ℕ} {x : Fin N → E n} (hR : 1 ≤ R) (hC : C ≤ C')
    (hx : IsSparse (C' : ℝ) R x) : IsSparse (C : ℝ) R x := by
  intro i j hij
  refine le_trans ?_ (hx i j hij)
  have hN : (1 : ℝ) ≤ N := by
    have : 0 < N := Fin.pos i
    exact_mod_cast this
  rw [← Real.mul_rpow (by linarith) (by linarith), ← Real.mul_rpow (by linarith) (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_mul_of_one_le_of_one_le hR hN)
    (by exact_mod_cast hC)

/-- Translating a piece to the origin: same `|ĝ|`, same `Lᵖ` integrals. -/
lemma exists_translate (g : 𝓢(E n, ℂ)) (c : E n) (hg : tsupport g ⊆ closedBall c R) :
    ∃ h : 𝓢(E n, ℂ), tsupport h ⊆ closedBall 0 R ∧
      (∀ η, ‖𝓕 (h : E n → ℂ) η‖ₑ = ‖𝓕 (g : E n → ℂ) η‖ₑ) ∧
      ∀ p : ℝ, ∫⁻ y, ‖h y‖ₑ ^ p = ∫⁻ y, ‖g y‖ₑ ^ p := by
  have hsupp : tsupport (fun y => g (y + c)) ⊆ closedBall 0 R := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    have : y + c ∈ closedBall c R := hg (subset_tsupport _ hy)
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right] at this
    rwa [mem_closedBall_zero_iff]
  have hc : HasCompactSupport (fun y => g (y + c)) :=
    (isCompact_closedBall (0 : E n) R).of_isClosed_subset (isClosed_tsupport _) hsupp
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun y => g (y + c)) :=
    (g.smooth ⊤).comp (contDiff_id.add contDiff_const)
  refine ⟨hc.toSchwartzMap hcd, hsupp, fun η => ?_, fun p => ?_⟩
  · change ‖𝓕 (fun y => g (y + c)) η‖ₑ = _
    rw [Real.fourier_eq, Real.fourier_eq]
    have e : ∀ y : E n, 𝐞 (-⟪y, η⟫) • g (y + c) =
        (𝐞 ⟪c, η⟫ : ℂ) • (𝐞 (-⟪y + c, η⟫) • g (y + c)) := by
      intro y
      rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      have : ⟪c, η⟫ + -⟪y + c, η⟫ = -⟪y, η⟫ := by rw [inner_add_left]; ring
      rw [this]
    simp_rw [e]
    rw [integral_smul, integral_add_right_eq_self (fun z => 𝐞 (-⟪z, η⟫) • g z) c, enorm_smul]
    have h1 : ‖((𝐞 ⟪c, η⟫ : Circle) : ℂ)‖ₑ = 1 := by
      rw [← ofReal_norm, Circle.norm_coe, ENNReal.ofReal_one]
    rw [h1, one_mul]
  · change ∫⁻ y, ‖g (y + c)‖ₑ ^ p = _
    exact lintegral_add_right_eq_self (fun y => ‖g y‖ₑ ^ p) c

/-- Modulating a piece: `y ↦ 𝐞(⟪y, v⟫) f y` has transform `f̂(· - v)` and the same modulus. -/
lemma exists_modulate (f : 𝓢(E n, ℂ)) (hf : tsupport f ⊆ closedBall 0 R) (v : E n) :
    ∃ h : 𝓢(E n, ℂ), tsupport h ⊆ closedBall 0 R ∧
      (∀ ω, 𝓕 (h : E n → ℂ) ω = 𝓕 (f : E n → ℂ) (ω - v)) ∧ ∀ y, ‖h y‖ₑ = ‖f y‖ₑ := by
  set h0 : E n → ℂ := fun y => (𝐞 ⟪y, v⟫ : ℂ) * f y with hh0
  have hsupp : tsupport h0 ⊆ closedBall 0 R := tsupport_mul_subset_right.trans hf
  have hc : HasCompactSupport h0 :=
    (isCompact_closedBall (0 : E n) R).of_isClosed_subset (isClosed_tsupport _) hsupp
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => (𝐞 ⟪y, v⟫ : ℂ)) := by
    simp_rw [Real.fourierChar_apply]
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => ⟪y, v⟫) := contDiff_id.inner ℝ contDiff_const
    exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul hlin)).mul contDiff_const)
  have hcd : ContDiff ℝ (⊤ : ℕ∞) h0 := he.mul (f.smooth ⊤)
  refine ⟨hc.toSchwartzMap hcd, hsupp, fun ω => ?_, fun y => ?_⟩
  · change 𝓕 h0 ω = _
    rw [Real.fourier_eq, Real.fourier_eq]
    congr 1; ext y
    simp only [hh0, Circle.smul_def, smul_eq_mul]
    have : -⟪y, ω - v⟫ = -⟪y, ω⟫ + ⟪y, v⟫ := by rw [inner_sub_right]; ring
    rw [this, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  · change ‖h0 y‖ₑ = _
    simp only [hh0, enorm_mul]
    rw [← ofReal_norm (𝐞 _ : ℂ), Circle.norm_coe, ENNReal.ofReal_one, one_mul]

end TaoBR.Tao49.PartW2
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise
namespace TaoBR.Tao49.PartW2
variable {n : ℕ}
/-! ## The smoothed input -/
lemma fourier_PhiS (ω : E n) : 𝓕 (PhiS n : E n → ℂ) ω = phi n (-ω) := by
  rw [Real.fourier_eq, phi_eq]
  congr 1; ext y
  rw [Circle.smul_def, smul_eq_mul, inner_neg_right]
  rfl

lemma PhiS_tsupport : tsupport (PhiS n : E n → ℂ) ⊆ closedBall 0 1 := by
  have h1 : tsupport (PhiS n : E n → ℂ) ⊆ tsupport (Phi n) := by
    refine closure_mono (fun y hy => ?_)
    intro h0; apply hy
    change PhiC n y = 0
    simp [PhiC, h0]
  refine h1.trans ?_
  have hP : Phi n = (bump n).normed volume := rfl
  rw [hP, (bump n).tsupport_normed_eq]
  exact closedBall_subset_closedBall (by norm_num [bump])

/-- `R_μ(p, α)` forces `μ` to be locally finite. -/
lemma locallyFinite_of_restrMu {μ : Measure (E n)} {p α : ℝ} (hp : 1 ≤ p)
    (h : RestrMu μ p α) : IsLocallyFiniteMeasure μ := by
  obtain ⟨C, hC⟩ := h
  have hp0 : 0 < p := by linarith
  refine ⟨fun v => ⟨ball v 2, ball_mem_nhds v (by norm_num), ?_⟩⟩
  obtain ⟨h, hs, hF, -⟩ := exists_modulate (PhiS n) (PhiS_tsupport (n := n)) v
  have hb := hC 1 le_rfl h hs
  have hfin : eLpNorm (𝓕 (h : E n → ℂ)) (ENNReal.ofReal p) μ < ⊤ := by
    refine hb.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
      ENNReal.ofReal_lt_top) ?_)
    exact (h.memLp (ENNReal.ofReal p) volume).eLpNorm_lt_top
  have hp_ne : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hint := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_ne ENNReal.ofReal_ne_top hfin
  rw [ENNReal.toReal_ofReal hp0.le] at hint
  have hlow : ∀ ω, (ball v 2).indicator (fun _ => ((1 / 2 : ℝ≥0∞)) ^ p) ω ≤
      ‖𝓕 (h : E n → ℂ) ω‖ₑ ^ p := by
    intro ω
    by_cases hω : ω ∈ ball v 2
    · rw [indicator_of_mem hω]
      refine ENNReal.rpow_le_rpow ?_ hp0.le
      rw [hF ω, fourier_PhiS, ← ofReal_norm]
      have : ‖-(ω - v)‖ < 2 := by rw [norm_neg, ← dist_eq_norm]; exact hω
      have h2 := phi_lower n this
      calc (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
        _ ≤ _ := ENNReal.ofReal_le_ofReal h2
    · rw [indicator_of_notMem hω]; exact bot_le
  have h3 := (lintegral_mono hlow).trans_lt hint
  rw [lintegral_indicator_const measurableSet_ball] at h3
  have hc0 : ((1 / 2 : ℝ≥0∞)) ^ p ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hp0]
  have hct : ((1 / 2 : ℝ≥0∞)) ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp0.le (by simp)
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.mul_top hc0] at h3
  exact lt_irrefl _ h3

end TaoBR.Tao49.PartW2
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise
namespace TaoBR.Tao49.PartW2
/-- **W2a (the smoothed input).** Verbatim restatement of the Blueprint's `smoothed_of_restrMu`. -/
theorem smoothed_of_restrMu {n : ℕ} {μ : Measure (E n)} {p α : ℝ} (hp : 1 ≤ p)
    (h : RestrMu μ p α) :
    ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ closedBall 0 R →
      ∫⁻ η, ‖𝓕 (f : E n → ℂ) η‖ₑ ^ p * Wt μ R η ≤
        C * ENNReal.ofReal (R ^ α) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p := by
  have hlf := locallyFinite_of_restrMu hp h
  obtain ⟨C, hC⟩ := h
  have hp0 : 0 < p := by linarith
  refine ⟨C ^ p, fun R hR f hf => ?_⟩
  rw [ENNReal.coe_rpow_of_nonneg _ hp0.le]
  have hR0 : 0 < R := by linarith
  set M : ℝ≥0∞ := (C : ℝ≥0∞) ^ p * ENNReal.ofReal (R ^ α) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p
  set Fh : E n → ℝ≥0∞ := fun η => ‖𝓕 (f : E n → ℂ) η‖ₑ ^ p with hFh
  set k : E n → ℝ≥0∞ := fun v => ‖Kker n R 0 v‖ₑ with hk
  have hFm : Measurable Fh := (fourier_continuous f).measurable.enorm.pow_const p
  have hkm : Measurable k := K_continuous.measurable.enorm
  have hp_ne : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have key : ∀ v, ∫⁻ ω, Fh (ω - v) ∂μ ≤ M := by
    intro v
    obtain ⟨g, hgs, hgF, hgn⟩ := exists_modulate f hf v
    have hb := hC R hR g hgs
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne ENNReal.ofReal_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0.le] at hb
    have hb2 := ENNReal.rpow_le_rpow hb hp0.le
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one,
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
      ENNReal.rpow_one, ENNReal.mul_rpow_of_nonneg _ _ hp0.le] at hb2
    simp_rw [hgF, hgn] at hb2
    exact hb2
  have hm2 : Measurable (Function.uncurry fun (η ω : E n) => Fh η * k (ω - η)) :=
    (hFm.comp measurable_fst).mul (hkm.comp (measurable_snd.sub measurable_fst))
  have hm3 : Measurable (Function.uncurry fun (ω v : E n) => Fh (ω - v) * k v) :=
    (hFm.comp (measurable_fst.sub measurable_snd)).mul (hkm.comp measurable_snd)
  calc ∫⁻ η, Fh η * Wt μ R η
      = ∫⁻ η, ∫⁻ ω, Fh η * k (ω - η) ∂μ := by
        refine lintegral_congr (fun η => ?_)
        rw [Wt, ← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le enorm_ne_top)]
    _ = ∫⁻ ω, (∫⁻ η, Fh η * k (ω - η)) ∂μ := lintegral_lintegral_swap hm2.aemeasurable
    _ = ∫⁻ ω, (∫⁻ v, Fh (ω - v) * k v) ∂μ := by
        refine lintegral_congr (fun ω => ?_)
        rw [← lintegral_sub_left_eq_self (fun η => Fh η * k (ω - η)) ω]
        simp only [sub_sub_cancel]
    _ = ∫⁻ v, ∫⁻ ω, Fh (ω - v) * k v ∂μ := lintegral_lintegral_swap hm3.aemeasurable
    _ = ∫⁻ v, k v * ∫⁻ ω, Fh (ω - v) ∂μ := by
        refine lintegral_congr (fun v => ?_)
        rw [lintegral_mul_const' _ _ enorm_ne_top, mul_comm]
    _ ≤ ∫⁻ v, k v * M := lintegral_mono (fun v => by gcongr; exact key v)
    _ = M := by rw [lintegral_mul_const _ hkm, hk, K_lintegral hR0, one_mul]

end TaoBR.Tao49.PartW2
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
alias smoothed_of_restrMu := TaoBR.Tao49.PartW2.smoothed_of_restrMu

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise
namespace TaoBR.Tao49.PartW2
variable {n : ℕ}
/-! ## The floor term -/
/-- Hölder on a set: `(∫ |g|)^p ≤ |s|^{p-1} ∫ |g|^p` for `g` vanishing off `s`. -/
lemma l1_rpow_le {p : ℝ} (hp : 1 < p) (g : E n → ℂ) (hg : Measurable g) {s : Set (E n)}
    (hs : MeasurableSet s) (h0 : ∀ y ∉ s, g y = 0) :
    (∫⁻ y, ‖g y‖ₑ) ^ p ≤ volume s ^ (p - 1) * ∫⁻ y, ‖g y‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have hpq := Real.HolderConjugate.conjExponent hp
  set q := p.conjExponent with hq
  have hq0 : 0 < q := hpq.symm.pos
  set a : E n → ℝ≥0∞ := s.indicator 1
  have ha : Measurable a := measurable_one.indicator hs
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hg.enorm.aemeasurable ha.aemeasurable
  have e1 : ∀ y, ‖g y‖ₑ * a y = ‖g y‖ₑ := by
    intro y
    by_cases hy : y ∈ s
    · simp [a, indicator_of_mem hy]
    · simp [h0 y hy]
  have e2 : ∀ y, a y ^ q = a y := by
    intro y
    by_cases hy : y ∈ s
    · simp [a, indicator_of_mem hy]
    · simp [a, indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hq0]
  simp only [Pi.mul_apply, e1, e2] at h
  rw [lintegral_indicator_one hs] at h
  have h2 := ENNReal.rpow_le_rpow h hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    one_div_mul_cancel hp0.ne', ENNReal.rpow_one] at h2
  have e3 : 1 / q * p = p - 1 := by
    rw [hq, Real.conjExponent]; field_simp
  rw [e3, mul_comm] at h2
  exact h2

lemma enorm_fourier_le (g : 𝓢(E n, ℂ)) (η : E n) :
    ‖𝓕 (g : E n → ℂ) η‖ₑ ≤ ∫⁻ y, ‖g y‖ₑ := by
  rw [Real.fourier_eq]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1; ext y
  rw [Circle.smul_def, smul_eq_mul, enorm_mul, ← ofReal_norm (𝐞 _ : ℂ), Circle.norm_coe,
    ENNReal.ofReal_one, one_mul]

/-- `V1 = |B(0, 1)|` (open ball), `V2 = |B(0, 2)|`. -/
noncomputable def V1 (n : ℕ) : ℝ≥0∞ := volume (ball (0 : E n) 1)

noncomputable def V2 (n : ℕ) : ℝ≥0∞ := volume (closedBall (0 : E n) 2)

lemma floor_bound {p : ℝ} (hp : 1 < p) (hp2 : p < 2) {R : ℝ} (hR : 1 ≤ R) (h : 𝓢(E n, ℂ))
    (hs : tsupport h ⊆ closedBall 0 R) :
    ∫⁻ η, (closedBall (0 : E n) 2).indicator (fun η => ‖𝓕 (h : E n → ℂ) η‖ₑ ^ p) η *
        ENNReal.ofReal (R ^ (-(n : ℝ))) ≤
      V2 n * V1 n ^ (p - 1) * ∫⁻ y, ‖h y‖ₑ ^ p := by
  have hR0 : 0 < R := by linarith
  have hp0 : 0 < p := by linarith
  set L := ∫⁻ y, ‖h y‖ₑ
  have hpt : ∀ η, (closedBall (0 : E n) 2).indicator (fun η => ‖𝓕 (h : E n → ℂ) η‖ₑ ^ p) η *
      ENNReal.ofReal (R ^ (-(n : ℝ))) ≤
      (closedBall (0 : E n) 2).indicator (fun _ => L ^ p * ENNReal.ofReal (R ^ (-(n : ℝ)))) η := by
    intro η
    by_cases hη : η ∈ closedBall (0 : E n) 2
    · rw [indicator_of_mem hη, indicator_of_mem hη]
      gcongr
      exact enorm_fourier_le h η
    · rw [indicator_of_notMem hη, indicator_of_notMem hη, zero_mul]
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_indicator_const measurableSet_closedBall]
  have h0 : ∀ y ∉ closedBall (0 : E n) R, h y = 0 :=
    fun y hy => image_eq_zero_of_notMem_tsupport (fun h' => hy (hs h'))
  have hH := l1_rpow_le hp h h.continuous.measurable measurableSet_closedBall h0
  rw [Measure.addHaar_closedBall _ _ hR0.le, finrank_euclideanSpace_fin] at hH
  have hRn : (1 : ℝ) ≤ R ^ n := one_le_pow₀ hR
  have hfl : ENNReal.ofReal (R ^ n) ^ (p - 1) * ENNReal.ofReal (R ^ (-(n : ℝ))) ≤ 1 := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.rpow_neg hR0.le, Real.rpow_natCast, ← Real.rpow_neg_one,
      ← Real.rpow_add (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hRn (by linarith)
  calc L ^ p * ENNReal.ofReal (R ^ (-(n : ℝ))) * V2 n
      ≤ (ENNReal.ofReal (R ^ n) * V1 n) ^ (p - 1) * (∫⁻ y, ‖h y‖ₑ ^ p) *
          ENNReal.ofReal (R ^ (-(n : ℝ))) * V2 n := by
        gcongr; exact hH
    _ = (ENNReal.ofReal (R ^ n) ^ (p - 1) * ENNReal.ofReal (R ^ (-(n : ℝ)))) *
          (V2 n * V1 n ^ (p - 1) * ∫⁻ y, ‖h y‖ₑ ^ p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]; ring
    _ ≤ 1 * (V2 n * V1 n ^ (p - 1) * ∫⁻ y, ‖h y‖ₑ ^ p) := by gcongr
    _ = _ := one_mul _

end TaoBR.Tao49.PartW2
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise
namespace TaoBR.Tao49.PartW2
lemma enorm_indicator_rpow {n : ℕ} {p : ℝ} (hp : 0 < p) (s : Set (E n)) (F : E n → ℂ) (η : E n) :
    ‖s.indicator F η‖ₑ ^ p = s.indicator (fun η => ‖F η‖ₑ ^ p) η := by
  by_cases h : η ∈ s
  · rw [indicator_of_mem h, indicator_of_mem h]
  · rw [indicator_of_notMem h, indicator_of_notMem h, enorm_zero, ENNReal.zero_rpow_of_pos hp]

/-- One piece: `∫ |G_i|^p (Wt + R^{-n}) ≤ (C_s + V2 V1^{p-1}) R^{αp} ∫ |g_i|^p`. -/
lemma piece_bound {n : ℕ} {μ : Measure (E n)} [SFinite μ] {p α : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hα : 0 ≤ α) {Cs : ℝ≥0} {R : ℝ} (hR : 1 ≤ R)
    (hCs : ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ closedBall 0 R →
      ∫⁻ η, ‖𝓕 (f : E n → ℂ) η‖ₑ ^ p * Wt μ R η ≤
        Cs * ENNReal.ofReal (R ^ α) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p)
    (g : 𝓢(E n, ℂ)) (c : E n) (hg : tsupport g ⊆ closedBall c R) :
    ∫⁻ η, ‖(closedBall (0 : E n) 2).indicator (𝓕 (g : E n → ℂ)) η‖ₑ ^ p *
        (Wt μ R η + ENNReal.ofReal (R ^ (-(n : ℝ)))) ≤
      ((Cs : ℝ≥0∞) + V2 n * V1 n ^ (p - 1)) * ENNReal.ofReal (R ^ α) ^ p * ∫⁻ y, ‖g y‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  obtain ⟨h, hhs, hhF, hhL⟩ := exists_translate g c hg
  set B := closedBall (0 : E n) 2
  set fl := ENNReal.ofReal (R ^ (-(n : ℝ)))
  set X := ENNReal.ofReal (R ^ α) ^ p
  have hX : 1 ≤ X := by
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (R ^ α) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow hR hα)
    have := ENNReal.rpow_le_rpow h1 hp0.le
    rwa [ENNReal.one_rpow] at this
  have e0 : ∀ η, ‖B.indicator (𝓕 (g : E n → ℂ)) η‖ₑ ^ p =
      B.indicator (fun η => ‖𝓕 (h : E n → ℂ) η‖ₑ ^ p) η := by
    intro η
    rw [enorm_indicator_rpow hp0]
    simp_rw [hhF]
  simp_rw [e0, mul_add]
  have hm1 : Measurable (fun η => B.indicator (fun η => ‖𝓕 (h : E n → ℂ) η‖ₑ ^ p) η) :=
    ((fourier_continuous h).measurable.enorm.pow_const p).indicator measurableSet_closedBall
  rw [lintegral_add_left (f := fun η => B.indicator (fun η => ‖𝓕 (h : E n → ℂ) η‖ₑ ^ p) η *
    Wt μ R η) (hm1.mul (Wt_meas μ))]
  have t1 : ∫⁻ η, B.indicator (fun η => ‖𝓕 (h : E n → ℂ) η‖ₑ ^ p) η * Wt μ R η ≤
      Cs * X * ∫⁻ y, ‖g y‖ₑ ^ p := by
    rw [← hhL p]
    refine le_trans (lintegral_mono (fun η => ?_)) (hCs h hhs)
    gcongr
    exact indicator_le_self _ _ η
  have t2 := floor_bound hp hp2 hR h hhs
  rw [hhL p] at t2
  have hV : V2 n * V1 n ^ (p - 1) ≤ V2 n * V1 n ^ (p - 1) * X := le_mul_of_one_le_right zero_le hX
  calc _ ≤ Cs * X * (∫⁻ y, ‖g y‖ₑ ^ p) + V2 n * V1 n ^ (p - 1) * (∫⁻ y, ‖g y‖ₑ ^ p) :=
        add_le_add t1 t2
    _ ≤ Cs * X * (∫⁻ y, ‖g y‖ₑ ^ p) + V2 n * V1 n ^ (p - 1) * X * (∫⁻ y, ‖g y‖ₑ ^ p) := by
        gcongr
    _ = _ := by ring

/-- **W2 (Lemma 3.2, assembly).** Verbatim restatement of the Blueprint's `sparse_of_restrMu`. -/
theorem sparse_of_restrMu {n : ℕ} (hn : 2 ≤ n) {μ : Measure (E n)} {S : Set (E n)}
    (hμ : DecayMeasure μ S) {C0 : ℕ} (hC0 : 3 * n + 3 ≤ C0) {A2 : ℝ} (hA2 : 0 ≤ A2)
    (hL2 : ∀ R : ℝ, 1 ≤ R → ∀ (N : ℕ) (x : Fin N → E n), IsSparse (C0 : ℝ) R x →
      ∀ G : Fin N → E n → ℂ, (∀ i, Measurable (G i)) → (∀ i, ∃ B : ℝ, ∀ η, ‖G i η‖ ≤ B) →
        (∀ i η, η ∉ closedBall (0 : E n) 2 → G i η = 0) →
        ∫⁻ ω, ‖Top R x G ω‖ₑ ^ (2 : ℝ) ∂μ ≤
          ENNReal.ofReal A2 * ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ (2 : ℝ) *
            (Wt μ R η + ENNReal.ofReal (R ^ (-(n : ℝ)))))
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2) {α : ℝ} (hα : 0 ≤ α) (hT : RestrMu μ p α) :
    ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ (N : ℕ) (x : Fin N → E n), IsSparse (C0 : ℝ) R x →
      ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ ⋃ i, closedBall (x i) R →
        eLpNorm (𝓕 (f : E n → ℂ)) (ENNReal.ofReal p) μ ≤
          C * ENNReal.ofReal (R ^ α) * eLpNorm f (ENNReal.ofReal p) volume := by
  have := hμ.finite
  obtain ⟨Cs, hCs⟩ := smoothed_of_restrMu hp.le hT
  have hS : ∀ᵐ ω ∂μ, ω ∈ S := mem_ae_iff.2 hμ.null_compl
  have hq0 : 0 < p := by linarith
  set A := 1 + A2 with hA_def
  set Cm := ENNReal.ofReal (p * (2 / (p - 1) + 4 / (2 - p))) with hCm
  set Cin : ℝ≥0∞ := (Cs : ℝ≥0∞) + V2 n * V1 n ^ (p - 1) with hCin
  set K0 : ℝ≥0∞ := Cm * ENNReal.ofReal A * Cin * 2 ^ p with hK0_def
  have hCin_ne : Cin ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, ENNReal.mul_ne_top ?_ ?_⟩
    · exact measure_closedBall_lt_top.ne
    · exact ENNReal.rpow_ne_top_of_nonneg (by linarith) measure_ball_lt_top.ne
  have hK0 : K0 ≠ ⊤ := by
    simp only [hK0_def]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top) hCin_ne) ?_
    exact ENNReal.rpow_ne_top_of_nonneg hq0.le (by simp)
  refine ⟨(K0 ^ (1 / p)).toNNReal, ?_⟩
  intro R hR N x hx f hf
  have hR0 : 0 < R := by linarith
  obtain ⟨g, hgs, hfg, hgsum⟩ := decomp n hn hR x (isSparse_mono hR hC0 hx) f hf hq0
  set G : Fin N → E n → ℂ := fun i => (closedBall (0 : E n) 2).indicator (𝓕 (g i : E n → ℂ))
    with hG_def
  have hPG : PG G := PG_G g
  set fl := ENNReal.ofReal (R ^ (-(n : ℝ))) with hfl
  set w : E n → ℝ≥0∞ := fun η => Wt μ R η + fl with hw
  have hwm : Measurable w := (Wt_meas μ).add measurable_const
  set ν0 := (volume : Measure (E n)).withDensity w with hν0
  have hν : ∀ F : E n → ℝ≥0∞, Measurable F → ∫⁻ η, F η ∂ν0 = ∫⁻ η, F η * w η := by
    intro F hF
    rw [lintegral_withDensity_eq_lintegral_mul _ hwm hF]
    congr 1; ext η; simp only [Pi.mul_apply]; ring
  have hA1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal A := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hA2' : ENNReal.ofReal A2 ≤ ENNReal.ofReal A := ENNReal.ofReal_le_ofReal (by linarith)
  have h1 : ∀ G : Fin N → E n → ℂ, PG G →
      ∫⁻ ω, ‖Top R x G ω‖ₑ ∂μ ≤ ENNReal.ofReal A * ∑ i, ∫⁻ η, ‖G i η‖ₑ ∂ν0 := by
    intro G hG
    refine (Top_L1 G (fun i => (hG i).1)).trans ?_
    calc ∑ i, ∫⁻ η, ‖G i η‖ₑ * Wt μ R η ≤ ∑ i, ∫⁻ η, ‖G i η‖ₑ ∂ν0 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [hν _ (hG i).1.enorm]
          refine lintegral_mono (fun η => ?_)
          gcongr
          exact le_self_add
      _ = 1 * ∑ i, ∫⁻ η, ‖G i η‖ₑ ∂ν0 := (one_mul _).symm
      _ ≤ _ := by gcongr
  have h2 : ∀ G : Fin N → E n → ℂ, PG G →
      ∫⁻ ω, ‖Top R x G ω‖ₑ ^ (2 : ℝ) ∂μ ≤
        ENNReal.ofReal A * ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ (2 : ℝ) ∂ν0 := by
    intro G hG
    refine (hL2 R hR N x hx G (fun i => (hG i).1) (fun i => (hG i).2.1)
      (fun i => (hG i).2.2)).trans ?_
    calc _ ≤ ENNReal.ofReal A * ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ (2 : ℝ) * w η := by gcongr
      _ = _ := by
          congr 1
          exact Finset.sum_congr rfl (fun i _ => (hν _ ((hG i).1.enorm.pow_const _)).symm)
  have hmarc := marc ν0 μ PG (Top R x) (ENNReal.ofReal A)
    (fun G t hG => PG_truncHi hG t) (fun G t hG => PG_truncLo hG t)
    (fun G G' hG hG' => Top_add hR0 G G' (PG_integrable hG) (PG_integrable hG'))
    (fun G hG => Top_meas G (fun i => (hG i).1)) (fun G hG i => (hG i).1)
    h1 h2 hp hp2 G hPG
  have hTG : ∫⁻ ω, ‖𝓕 (f : E n → ℂ) ω‖ₑ ^ p ∂μ = ∫⁻ ω, ‖Top R x G ω‖ₑ ^ p ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hS] with ω hω
    have hω' : ‖ω‖ ≤ 3 / 2 := mem_closedBall_zero_iff.1 (hμ.subset hω)
    rw [fourier_eq_Top hR x f g hgs hfg hω']
  rw [← hTG] at hmarc
  have hin : ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ p ∂ν0 ≤
      Cin * ENNReal.ofReal (R ^ α) ^ p * ((2 : ℝ≥0∞) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p) := by
    calc ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ p ∂ν0
        ≤ ∑ i, Cin * ENNReal.ofReal (R ^ α) ^ p * ∫⁻ y, ‖g i y‖ₑ ^ p := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [hν _ ((hPG i).1.enorm.pow_const p)]
          exact piece_bound hp hp2 hα hR (hCs R hR) (g i) (x i) (hgs i)
      _ = Cin * ENNReal.ofReal (R ^ α) ^ p * ∑ i, ∫⁻ y, ‖g i y‖ₑ ^ p := by rw [Finset.mul_sum]
      _ ≤ _ := by gcongr
  have htot : ∫⁻ ω, ‖𝓕 (f : E n → ℂ) ω‖ₑ ^ p ∂μ ≤
      K0 * ENNReal.ofReal (R ^ α) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p := by
    refine hmarc.trans ?_
    calc Cm * ENNReal.ofReal A * ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ p ∂ν0
        ≤ Cm * ENNReal.ofReal A * (Cin * ENNReal.ofReal (R ^ α) ^ p *
            ((2 : ℝ≥0∞) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p)) := by gcongr
      _ = K0 * ENNReal.ofReal (R ^ α) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p := by rw [hK0_def]; ring
  -- take p-th roots
  have hq_ne : ENNReal.ofReal p ≠ 0 := by simpa using hq0
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq_ne ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hq_ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le, ENNReal.coe_toNNReal
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hK0)]
  calc (∫⁻ ω, ‖𝓕 (f : E n → ℂ) ω‖ₑ ^ p ∂μ) ^ (1 / p)
      ≤ (K0 * ENNReal.ofReal (R ^ α) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow htot (by positivity)
    _ = K0 ^ (1 / p) * ENNReal.ofReal (R ^ α) * (∫⁻ y, ‖f y‖ₑ ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hq0.ne', ENNReal.rpow_one]

end TaoBR.Tao49.PartW2
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
alias sparse_of_restrMu := TaoBR.Tao49.PartW2.sparse_of_restrMu

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace
namespace TaoBR.Tao49.PartC
variable {n : ℕ}
/-!
# Part C of the Theorem 4.9 Blueprint (port of `proofs/parab/PartC.lean`)
-/
/-- The indicator of a set, with value `1 : ℂ`. -/
noncomputable def ind (S : Set (E n)) : E n → ℂ := S.indicator fun _ => (1 : ℂ)

/-- The lattice point `k` as a point of `E n`. -/
noncomputable def latt (k : Fin n → ℤ) : E n := WithLp.toLp 2 (fun i => (k i : ℝ))

lemma latt_apply (k : Fin n → ℤ) (i : Fin n) : latt k i = (k i : ℝ) := rfl

/-- The `c`-cube as a box of `Fin n → ℝ`. -/
lemma cCube_eq (c : ℝ) (k : Fin n → ℤ) :
    cCube c k = (WithLp.ofLp : E n → (Fin n → ℝ)) ⁻¹'
      Set.pi Set.univ (fun i => Set.Icc ((k i : ℝ) - c / 2) (k i + c / 2)) := by
  ext x
  simp only [cCube, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  show (∀ i, |x i - k i| ≤ c / 2) ↔ _
  constructor
  · intro h i; have := abs_le.mp (h i); exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · intro h i; have := h i; exact abs_le.mpr ⟨by linarith [this.1], by linarith [this.2]⟩

lemma measurableSet_cCube (c : ℝ) (k : Fin n → ℤ) : MeasurableSet (cCube c k) := by
  rw [cCube_eq]
  exact (MeasurableSet.univ_pi fun i => measurableSet_Icc).preimage
    (WithLp.measurable_ofLp 2 _)

lemma volume_cCube {c : ℝ} (hc : 0 ≤ c) (k : Fin n → ℤ) :
    volume (cCube c k) = ENNReal.ofReal c ^ n := by
  rw [cCube_eq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    ((MeasurableSet.univ_pi fun i => measurableSet_Icc).nullMeasurableSet), volume_pi,
    Measure.pi_pi]
  have : ∀ i : Fin n, ((k i : ℝ) + c / 2 - (k i - c / 2)) = c := fun i => by ring
  simp only [Real.volume_Icc, this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma volume_cCube_lt_top (c : ℝ) (k : Fin n → ℤ) : volume (cCube c k) < ⊤ := by
  have hsub : cCube c k ⊆ cCube |c| k := fun x hx i => (hx i).trans (by
    have := le_abs_self c; linarith)
  calc volume (cCube c k) ≤ volume (cCube |c| k) := measure_mono hsub
    _ < ⊤ := by rw [volume_cCube (abs_nonneg c)]; exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

lemma cCube_disjoint {c : ℝ} (hc1 : c < 1) {k k' : Fin n → ℤ} (h : k ≠ k') :
    Disjoint (cCube c k) (cCube c k') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  have h1 := hx i
  have h2 := hx' i
  have : (1 : ℝ) ≤ |(k i : ℝ) - k' i| := by
    have : k i - k' i ≠ 0 := sub_ne_zero.mpr hi
    have h3 : (1 : ℤ) ≤ |k i - k' i| := Int.one_le_abs this
    exact_mod_cast h3
  have : |(k i : ℝ) - k' i| ≤ |x i - k i| + |x i - k' i| := by
    calc |(k i : ℝ) - k' i| = |(x i - k' i) - (x i - k i)| := by ring_nf
      _ ≤ |x i - k' i| + |x i - k i| := abs_sub _ _
      _ = _ := add_comm _ _
  linarith

lemma mem_cCube_iff_sub (c : ℝ) (k : Fin n → ℤ) (x : E n) :
    x ∈ cCube c k ↔ x - latt k ∈ cCube c 0 := by
  simp only [cCube, Set.mem_ofPred_eq, PiLp.sub_apply, latt_apply, Pi.zero_apply, Int.cast_zero,
    sub_zero]

/-- The Fourier transform of the indicator of the `c`-cube at `k`. -/
noncomputable def phi (c : ℝ) (k : Fin n → ℤ) (ω : E n) : ℂ := 𝓕 (ind (cCube c k)) ω

lemma integrable_ind_cCube (c : ℝ) (k : Fin n → ℤ) : Integrable (ind (cCube c k)) := by
  unfold ind
  exact (integrableOn_const (volume_cCube_lt_top c k).ne).integrable_indicator
    (measurableSet_cCube c k)

lemma norm_phi_le {c : ℝ} (hc : 0 ≤ c) (k : Fin n → ℤ) (ω : E n) : ‖phi c k ω‖ ≤ c ^ n := by
  unfold phi
  rw [fourier_eq]
  calc ‖∫ v, 𝐞 (-⟪v, ω⟫) • ind (cCube c k) v‖ ≤ ∫ v, ‖𝐞 (-⟪v, ω⟫) • ind (cCube c k) v‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ v, (cCube c k).indicator (fun _ => (1 : ℝ)) v := by
        congr 1; ext v
        by_cases hv : v ∈ cCube c k <;> simp [ind, Set.indicator, hv, Circle.norm_smul]
    _ = c ^ n := by
        rw [integral_indicator (measurableSet_cCube c k), setIntegral_const, smul_eq_mul, mul_one,
          measureReal_def, volume_cCube hc, ENNReal.toReal_pow, ENNReal.toReal_ofReal hc]

lemma phi_translate (c : ℝ) (k : Fin n → ℤ) (ω : E n) :
    phi c k ω = 𝐞 (-⟪latt k, ω⟫) • phi c 0 ω := by
  unfold phi
  rw [fourier_eq, fourier_eq]
  simp only [Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  rw [← integral_add_right_eq_self (μ := (volume : Measure (E n))) _ (latt k)]
  congr 1; ext v
  have hind : ind (cCube c k) (v + latt k) = ind (cCube c 0) v := by
    have : v + latt k ∈ cCube c k ↔ v ∈ cCube c 0 := by
      rw [mem_cCube_iff_sub c k, add_sub_cancel_right]
    by_cases hv : v ∈ cCube c 0
    · simp [ind, Set.indicator, hv, this.mpr hv]
    · simp [ind, Set.indicator, hv, mt this.mp hv]
  rw [hind, inner_add_left, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

lemma continuous_phi (c : ℝ) (k : Fin n → ℤ) : Continuous (phi c k) := by
  unfold phi
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simpa using (continuous_inner : Continuous fun p : E n × E n => ⟪p.1, p.2⟫))
    (integrable_ind_cCube c k)

/-- The one-dimensional factor of the transform of the `c`-cube. -/
noncomputable def fac (c s : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(c / 2)) (c / 2), ((𝐞 (-(t * s)) : ℂ))

lemma integral_cos_mul_sym {c s : ℝ} (hc : 0 < c) :
    ∫ t in Set.Icc (-(c / 2)) (c / 2), Real.cos (2 * π * s * t) =
      if s = 0 then c else Real.sin (π * c * s) / (π * s) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  split_ifs with hs
  · subst hs; simp
  · have hd : 2 * π * s ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun t => Real.cos t) hd, integral_cos]
    rw [show 2 * π * s * (c / 2) = π * c * s by ring,
      show 2 * π * s * -(c / 2) = -(π * c * s) by ring, Real.sin_neg, smul_eq_mul]
    field_simp
    ring

lemma re_fac {c s : ℝ} (hc : 0 < c) :
    (fac c s).re = if s = 0 then c else Real.sin (π * c * s) / (π * s) := by
  rw [← integral_cos_mul_sym hc, fac, ← RCLike.re_eq_complex_re, ← integral_re]
  · congr 1; ext t
    rw [RCLike.re_eq_complex_re, Real.fourierChar_apply, Complex.exp_ofReal_mul_I_re]
    rw [show 2 * π * -(t * s) = -(2 * π * s * t) by ring, Real.cos_neg]
  · exact (Continuous.integrableOn_Icc (by fun_prop))

lemma re_fac_pos {c s : ℝ} (hc : 0 < c) (hcs : c * |s| < 1) : 0 < (fac c s).re := by
  rw [re_fac hc]
  split_ifs with h0
  · exact hc
  · have key : Real.sin (π * c * s) / (π * s) = Real.sin (π * c * |s|) / (π * |s|) := by
      rcases le_or_gt 0 s with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, mul_neg, Real.sin_neg, mul_neg, neg_div_neg_eq]
    rw [key]
    have hs0 : 0 < |s| := abs_pos.mpr h0
    apply div_pos _ (by positivity)
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    calc π * c * |s| = π * (c * |s|) := by ring
      _ < π := mul_lt_of_lt_one_right Real.pi_pos hcs

lemma inner_toLp (y : Fin n → ℝ) (ω : E n) :
    ⟪(WithLp.toLp 2 y : E n), ω⟫ = ∑ i, y i * ω i := by
  simp [PiLp.inner_apply, mul_comm]

lemma phi_zero_eq_prod {c : ℝ} (ω : E n) : phi c 0 ω = ∏ i, fac c (ω i) := by
  unfold phi
  rw [fourier_eq, ← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  have : ∀ y : Fin n → ℝ, 𝐞 (-⟪(MeasurableEquiv.toLp 2 (Fin n → ℝ) y : E n), ω⟫) •
      ind (cCube c 0) (MeasurableEquiv.toLp 2 (Fin n → ℝ) y) =
      ∏ i, (Set.Icc (-(c / 2)) (c / 2)).indicator (fun t => ((𝐞 (-(t * ω i)) : ℂ))) (y i) := by
    intro y
    simp only [MeasurableEquiv.coe_toLp]
    rw [inner_toLp, Circle.smul_def, smul_eq_mul]
    by_cases hy : ∀ i, y i ∈ Set.Icc (-(c / 2)) (c / 2)
    · have hmem : (WithLp.toLp 2 y : E n) ∈ cCube c 0 := by
        intro i
        simp only [Pi.zero_apply, Int.cast_zero, sub_zero]
        exact abs_le.mpr (hy i)
      rw [ind, Set.indicator_of_mem hmem, mul_one]
      rw [Finset.prod_congr rfl (fun i _ => Set.indicator_of_mem (hy i) _)]
      simp only [Real.fourierChar_apply]
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
    · push_neg at hy
      obtain ⟨i, hi⟩ := hy
      have hnmem : (WithLp.toLp 2 y : E n) ∉ cCube c 0 := by
        intro h
        apply hi
        have := h i
        simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at this
        exact abs_le.mp this
      rw [ind, Set.indicator_of_notMem hnmem, mul_zero]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
  calc _ = ∫ y : Fin n → ℝ, ∏ i, (Set.Icc (-(c / 2)) (c / 2)).indicator
        (fun t => ((𝐞 (-(t * ω i)) : ℂ))) (y i) := integral_congr_ae (Filter.Eventually.of_forall this)
    _ = _ := ?_
  rw [integral_fintype_prod_volume_eq_prod]
  congr 1; ext i
  rw [fac, integral_indicator measurableSet_Icc]

lemma phi_zero_ne_zero {c : ℝ} (hc : 0 < c) {ω : E n} (hω : c * ‖ω‖ < 1) :
    phi c 0 ω ≠ 0 := by
  rw [phi_zero_eq_prod]
  rw [Finset.prod_ne_zero_iff]
  intro i _
  have hi : c * |ω i| < 1 := by
    have := PiLp.norm_apply_le ω i
    simp only [Real.norm_eq_abs] at this
    calc c * |ω i| ≤ c * ‖ω‖ := by gcongr
      _ < 1 := hω
  intro h0
  have := re_fac_pos hc hi
  rw [h0, Complex.zero_re] at this
  exact lt_irrefl _ this

/-- The transform of the `c`-cube is bounded below on `closedBall 0 r` when `c r < 1`. -/
lemma exists_lower_bound_phi {c r : ℝ} (hc : 0 < c) (hcr : c * r < 1) :
    ∃ m : ℝ, 0 < m ∧ ∀ ω : E n, ‖ω‖ ≤ r → m ≤ ‖phi c 0 ω‖ := by
  by_cases hne : (closedBall (0 : E n) r).Nonempty
  · obtain ⟨ω₀, hω₀, hmin⟩ := (isCompact_closedBall (0 : E n) r).exists_isMinOn hne
      (continuous_norm.comp (continuous_phi c 0)).continuousOn
    refine ⟨‖phi c 0 ω₀‖, ?_, ?_⟩
    · apply norm_pos_iff.mpr
      apply phi_zero_ne_zero hc
      rw [mem_closedBall_zero_iff] at hω₀
      calc c * ‖ω₀‖ ≤ c * r := by gcongr
        _ < 1 := hcr
    · intro ω hω
      exact hmin (mem_closedBall_zero_iff.mpr hω)
  · refine ⟨1, one_pos, fun ω hω => ?_⟩
    exact absurd ⟨ω, mem_closedBall_zero_iff.mpr hω⟩ hne

/-- `∑ a_k φ_k`: the Fourier transform of a function constant on `c`-cubes. -/
noncomputable def cubeSum (c : ℝ) (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ)
    (ω : E n) : ℂ := ∑ k ∈ s, a k * phi c k ω

lemma continuous_cubeSum (c : ℝ) (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ) :
    Continuous (cubeSum c s a) := by
  unfold cubeSum
  exact continuous_finset_sum _ fun k _ =>
    continuous_const.mul (continuous_phi c k)

lemma aesm_cubeSum {μ : Measure (E n)} (c : ℝ) (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ) :
    AEStronglyMeasurable (cubeSum c s a) μ :=
  (continuous_cubeSum c s a).aestronglyMeasurable

lemma cubeSum_add (c : ℝ) (s : Finset (Fin n → ℤ)) (a a' : (Fin n → ℤ) → ℂ) :
    cubeSum c s (fun k => a k + a' k) = cubeSum c s a + cubeSum c s a' := by
  funext ω; simp only [cubeSum, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma norm_cubeSum_le {c : ℝ} (hc : 0 ≤ c) (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ)
    (ω : E n) : ‖cubeSum c s a ω‖ ≤ ∑ k ∈ s, ‖a k‖ * c ^ n := by
  unfold cubeSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_phi_le hc k _) (norm_nonneg _)

lemma restriction_cubeFun (c : ℝ) (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ) :
    𝓕 (fun x => ∑ k ∈ s, a k * ind (cCube c k) x) = cubeSum c s a := by
  funext ω
  simp only [cubeSum, phi, fourier_eq, Finset.smul_sum]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_const_mul]
    congr 1; ext v
    simp only [Circle.smul_def, smul_eq_mul]
    try ring
  · intro k _
    have := (Real.fourierIntegral_convergent_iff (ω : E n)).2
      ((integrable_ind_cCube c k).const_mul (a k))
    refine this.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [Circle.smul_def, smul_eq_mul]
    try ring

lemma ind_iUnion_eq_sum {c : ℝ} (hc1 : c < 1) (t : Finset (Fin n → ℤ)) (x : E n) :
    (⋃ k ∈ t, cCube c k).indicator (fun _ => (1 : ℂ)) x = ∑ k ∈ t, 1 * ind (cCube c k) x := by
  by_cases hx : ∃ k ∈ t, x ∈ cCube c k
  · obtain ⟨k, hk, hxk⟩ := hx
    rw [Set.indicator_of_mem (Set.mem_iUnion₂.mpr ⟨k, hk, hxk⟩)]
    rw [Finset.sum_eq_single k]
    · simp [ind, hxk]
    · intro k' _ hk'
      have : x ∉ cCube c k' := fun h => Set.disjoint_left.mp (cCube_disjoint hc1 hk') h hxk
      simp [ind, this]
    · intro h; exact absurd hk h
  · simp only [not_exists, not_and] at hx
    rw [Set.indicator_of_notMem]
    · symm; apply Finset.sum_eq_zero; intro k hk; simp [ind, hx k hk]
    · simp only [Set.mem_iUnion]; rintro ⟨k, hk, h⟩; exact hx k hk h

lemma volume_iUnion_cCube {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) (t : Finset (Fin n → ℤ)) :
    volume (⋃ k ∈ t, cCube c k) = t.card * ENNReal.ofReal c ^ n := by
  rw [measure_biUnion_finset (fun k _ k' _ hk => cCube_disjoint hc1 hk)
    (fun k _ => measurableSet_cCube c k)]
  simp [volume_cCube hc]

lemma restriction_iUnion {c : ℝ} (hc1 : c < 1) (t : Finset (Fin n → ℤ)) :
    𝓕 ((⋃ k ∈ t, cCube c k).indicator fun _ => (1 : ℂ)) = cubeSum c t (fun _ => 1) := by
  rw [← restriction_cubeFun]
  congr 1; funext x; exact ind_iUnion_eq_sum hc1 t x

/-! ### The Riemann sum bound -/
lemma bernoulli_step {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h)
    (hxh : h ≤ x) : h * x ^ (-a) ≤ (x ^ (1 - a) - (x - h) ^ (1 - a)) / (1 - a) := by
  have hr : 0 < 1 - a := by linarith
  rw [le_div_iff₀ hr]
  have hb := rpow_one_add_le_one_add_mul_self (s := -(h / x)) (p := 1 - a)
    (by rw [neg_le_neg_iff, div_le_one hx]; exact hxh) hr.le (by linarith)
  have h1 : 1 + -(h / x) = (x - h) / x := by field_simp; ring
  rw [h1, Real.div_rpow (by linarith) hx.le] at hb
  have hxr : 0 < x ^ (1 - a) := Real.rpow_pos_of_pos hx _
  rw [div_le_iff₀ hxr] at hb
  have hxa : x ^ (1 - a) = x * x ^ (-a) := by
    rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]
  rw [hxa] at hb ⊢
  have : (1 + (1 - a) * -(h / x)) * (x * x ^ (-a)) = x * x ^ (-a) - (1 - a) * h * x ^ (-a) := by
    field_simp; ring
  rw [this] at hb
  nlinarith

lemma riemann_sum_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (L : ℕ) (hL : 1 ≤ L) :
    (1 / (L : ℝ)) * ∑ j ∈ Finset.range L, (((j : ℝ) + 1) / L) ^ (-a) ≤ 1 / (1 - a) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hstep : ∀ j ∈ Finset.range L, (1 / (L : ℝ)) * (((j : ℝ) + 1) / L) ^ (-a) ≤
      ((((j : ℝ) + 1) / L) ^ (1 - a) - ((j : ℝ) / L) ^ (1 - a)) / (1 - a) := by
    intro j _
    have := bernoulli_step ha0 ha1 (x := ((j : ℝ) + 1) / L) (h := 1 / L) (by positivity)
      (by positivity) (by gcongr; linarith)
    convert this using 3
    field_simp; ring
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [← Finset.sum_div]
  have := Finset.sum_range_sub (fun j : ℕ => ((j : ℝ) / L) ^ (1 - a)) L
  push_cast at this
  rw [this]
  simp only [Nat.cast_zero, zero_div]
  rw [div_self hL'.ne', Real.one_rpow, Real.zero_rpow (by linarith), sub_zero]

end TaoBR.Tao49.PartC
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace
namespace TaoBR.Tao49.PartC
variable {n : ℕ} {μ : Measure (E n)}
lemma eLpNorm_le_of_bound {G : E n → ℂ} {B : ℝ} (q : ℝ≥0∞)
    (h : ∀ ω, ‖G ω‖ ≤ B) :
    eLpNorm G q μ ≤ μ Set.univ ^ q.toReal⁻¹ * ENNReal.ofReal B :=
  eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall h)

lemma range_filter_card (L a : ℕ) (ha : a ≤ L) :
    ((Finset.range L).filter (fun j => j + 1 ≤ a)).card = a := by
  have : (Finset.range L).filter (fun j => j + 1 ≤ a) = Finset.range a := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.card_range]

lemma level_decomp (c : ℝ) (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℕ) (L : ℕ)
    (ha : ∀ k ∈ s, a k ≤ L) :
    cubeSum c s (fun k => (a k : ℂ) * (1 / (L : ℂ))) =
      (1 / (L : ℂ)) • ∑ j ∈ Finset.range L,
        cubeSum c (s.filter (fun k => j + 1 ≤ a k)) (fun _ => 1) := by
  funext ω
  simp only [cubeSum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, one_mul]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.sum_filter, Finset.sum_const, range_filter_card L (a k) (ha k hk), nsmul_eq_mul]
  ring

/-- The constant of the bound for nonnegative coefficients. -/
noncomputable def K2 (μ : Measure (E n)) (q q₀ A : ℝ) : ℝ≥0∞ :=
  2 * (μ Set.univ ^ (ENNReal.ofReal q).toReal⁻¹) + ENNReal.ofReal (A / (1 - q / q₀))

end TaoBR.Tao49.PartC
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace
namespace TaoBR.Tao49.PartC
variable {n : ℕ} {μ : Measure (E n)}
variable {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {q q₀ A : ℝ} (hq : 1 ≤ q) (hqq : q < q₀) (hA : 0 ≤ A)
  (h4 : ∀ t : Finset (Fin n → ℤ), eLpNorm (cubeSum c t (fun _ => 1)) (ENNReal.ofReal q)
      μ ≤ ENNReal.ofReal (A * ((t.card : ℝ) * c ^ n) ^ (1 / q₀)))
include hc hq hqq hA h4
lemma level_bound (s : Finset (Fin n → ℤ)) (b : (Fin n → ℤ) → ℝ) (hb : ∀ k, 0 ≤ b k)
    (hT : ∑ k ∈ s, b k ^ q * c ^ n ≤ 1) (a : (Fin n → ℤ) → ℕ) (L : ℕ) (hL : 1 ≤ L)
    (haL : ∀ k ∈ s, a k ≤ L) (hab : ∀ k ∈ s, (a k : ℝ) ≤ L * b k) :
    eLpNorm (cubeSum c s (fun k => (a k : ℂ) * (1 / (L : ℂ)))) (ENNReal.ofReal q)
      μ ≤ ENNReal.ofReal (A / (1 - q / q₀)) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hq0 : 0 < q₀ := by linarith
  set a' := q / q₀ with ha'
  have ha0 : 0 ≤ a' := div_nonneg (by linarith) hq0.le
  have ha1 : a' < 1 := (div_lt_one hq0).mpr hqq
  rw [level_decomp c s a L haL, eLpNorm_const_smul]
  -- each level
  have hlev : ∀ j ∈ Finset.range L,
      eLpNorm (cubeSum c (s.filter (fun k => j + 1 ≤ a k)) (fun _ => 1)) (ENNReal.ofReal q)
        μ ≤ ENNReal.ofReal (A * (((j : ℝ) + 1) / L) ^ (-a')) := by
    intro j _
    refine (h4 _).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ hA
    set t := s.filter (fun k => j + 1 ≤ a k)
    have hx : 0 < ((j : ℝ) + 1) / L := div_pos (by positivity) hL'
    have hcheb : (t.card : ℝ) * c ^ n ≤ ((((j : ℝ) + 1) / L) ^ q)⁻¹ := by
      have hxq : 0 < (((j : ℝ) + 1) / L) ^ q := Real.rpow_pos_of_pos hx q
      rw [← one_div, le_div_iff₀ hxq]
      have : ∀ k ∈ t, (((j : ℝ) + 1) / L) ^ q * c ^ n ≤ b k ^ q * c ^ n := by
        intro k hk
        rw [Finset.mem_filter] at hk
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply Real.rpow_le_rpow hx.le _ (by linarith)
        rw [div_le_iff₀ hL']
        have h1 : ((j : ℝ) + 1) ≤ a k := by exact_mod_cast hk.2
        linarith [hab k hk.1]
      have hsum := Finset.sum_le_sum this
      rw [Finset.sum_const, nsmul_eq_mul] at hsum
      have hsub : ∑ k ∈ t, b k ^ q * c ^ n ≤ ∑ k ∈ s, b k ^ q * c ^ n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => by have := hb k; positivity)
      nlinarith
    calc ((t.card : ℝ) * c ^ n) ^ (1 / q₀) ≤ (((((j : ℝ) + 1) / L) ^ q)⁻¹) ^ (1 / q₀) :=
          Real.rpow_le_rpow (by positivity) hcheb (by positivity)
      _ = (((j : ℝ) + 1) / L) ^ (-a') := by
          rw [← Real.rpow_neg hx.le, ← Real.rpow_mul hx.le]
          congr 1; rw [ha']; ring
  calc ‖(1 / (L : ℂ))‖ₑ * eLpNorm (∑ j ∈ Finset.range L,
          cubeSum c (s.filter (fun k => j + 1 ≤ a k)) (fun _ => 1)) (ENNReal.ofReal q)
          μ
        ≤ ‖(1 / (L : ℂ))‖ₑ * ∑ j ∈ Finset.range L,
          ENNReal.ofReal (A * (((j : ℝ) + 1) / L) ^ (-a')) := by
          gcongr
          refine (eLpNorm_sum_le (fun j _ => aesm_cubeSum _ _ _)
            (by rw [ENNReal.one_le_ofReal]; exact hq)).trans ?_
          exact Finset.sum_le_sum hlev
    _ = ENNReal.ofReal (A * ((1 / (L : ℝ)) *
          ∑ j ∈ Finset.range L, (((j : ℝ) + 1) / L) ^ (-a'))) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
          have : ‖(1 / (L : ℂ))‖ₑ = ENNReal.ofReal (1 / (L : ℝ)) := by
            rw [← ofReal_norm_eq_enorm]; congr 1
            rw [norm_div, norm_one, Complex.norm_natCast]
          rw [this, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ENNReal.ofReal (A / (1 - q / q₀)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [div_eq_mul_one_div A]
          exact mul_le_mul_of_nonneg_left (riemann_sum_le ha0 ha1 L hL) hA

lemma cube_bound_nonneg (s : Finset (Fin n → ℤ)) (b : (Fin n → ℤ) → ℝ) (hb : ∀ k, 0 ≤ b k)
    (hT : ∑ k ∈ s, b k ^ q * c ^ n ≤ 1) :
    eLpNorm (cubeSum c s (fun k => (b k : ℂ))) (ENNReal.ofReal q) μ ≤
      K2 μ q q₀ A := by
  set L : ℕ := ⌈(s.card : ℝ) * c ^ n⌉₊ + 1 with hLdef
  have hL : 1 ≤ L := by omega
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hLbig : (s.card : ℝ) * c ^ n ≤ L := by
    rw [hLdef]; push_cast; linarith [Nat.le_ceil ((s.card : ℝ) * c ^ n)]
  set u : (Fin n → ℤ) → ℝ := fun k => min (b k) 1
  set a : (Fin n → ℤ) → ℕ := fun k => ⌊(L : ℝ) * u k⌋₊
  have hu0 : ∀ k, 0 ≤ u k := fun k => le_min (hb k) zero_le_one
  have hu1 : ∀ k, u k ≤ 1 := fun k => min_le_right _ _
  have haL : ∀ k ∈ s, a k ≤ L := by
    intro k _
    have : (L : ℝ) * u k ≤ L := by nlinarith [hu1 k]
    exact Nat.floor_le_of_le (by exact_mod_cast this) |> fun h => by exact_mod_cast h
  have hab : ∀ k ∈ s, (a k : ℝ) ≤ L * b k := by
    intro k _
    have := Nat.floor_le (show 0 ≤ (L : ℝ) * u k by have := hu0 k; positivity)
    have hub : u k ≤ b k := min_le_left _ _
    calc (a k : ℝ) ≤ L * u k := this
      _ ≤ L * b k := by gcongr
  -- the three pieces
  set r : (Fin n → ℤ) → ℝ := fun k => u k - a k * (1 / L)
  set v : (Fin n → ℤ) → ℝ := fun k => b k - u k
  have hdec : (fun k => (b k : ℂ)) =
      fun k => ((a k : ℂ) * (1 / (L : ℂ)) + (r k : ℂ)) + (v k : ℂ) := by
    funext k; simp only [r, v]; push_cast; ring
  have hr : ∀ k, 0 ≤ r k ∧ r k ≤ 1 / L := by
    intro k
    have h1 := Nat.floor_le (show 0 ≤ (L : ℝ) * u k by have := hu0 k; positivity)
    have h2 := Nat.lt_floor_add_one ((L : ℝ) * u k)
    simp only [r]
    constructor
    · rw [sub_nonneg, mul_one_div, div_le_iff₀ hL']; linarith
    · have e : u k - (a k : ℝ) * (1 / L) = ((L : ℝ) * u k - a k) / L := by field_simp
      rw [e, div_le_div_iff_of_pos_right hL']; linarith
  have hv : ∀ k, 0 ≤ v k ∧ v k ≤ b k ^ q := by
    intro k
    simp only [v, u]
    constructor
    · linarith [min_le_left (b k) 1]
    · rcases le_total (b k) 1 with h | h
      · rw [min_eq_left h, sub_self]; exact Real.rpow_nonneg (hb k) _
      · rw [min_eq_right h]
        calc b k - 1 ≤ b k := by linarith
          _ = b k ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ b k ^ q := Real.rpow_le_rpow_of_exponent_le h hq
  rw [hdec, cubeSum_add, cubeSum_add]
  have hbound1 : eLpNorm (cubeSum c s (fun k => (r k : ℂ))) (ENNReal.ofReal q) μ ≤
      μ Set.univ ^ (ENNReal.ofReal q).toReal⁻¹ * ENNReal.ofReal 1 := by
    apply eLpNorm_le_of_bound
    intro ω
    refine (norm_cubeSum_le hc.le s _ ω).trans ?_
    calc ∑ k ∈ s, ‖(r k : ℂ)‖ * c ^ n ≤ ∑ k ∈ s, (1 / (L : ℝ)) * c ^ n := by
          gcongr with k hk
          rw [Complex.norm_real, Real.norm_of_nonneg (hr k).1]; exact (hr k).2
      _ = (s.card : ℝ) * c ^ n / L := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 1 := by rw [div_le_one hL']; exact hLbig
  have hbound2 : eLpNorm (cubeSum c s (fun k => (v k : ℂ))) (ENNReal.ofReal q) μ ≤
      μ Set.univ ^ (ENNReal.ofReal q).toReal⁻¹ * ENNReal.ofReal 1 := by
    apply eLpNorm_le_of_bound
    intro ω
    refine (norm_cubeSum_le hc.le s _ ω).trans ?_
    calc ∑ k ∈ s, ‖(v k : ℂ)‖ * c ^ n ≤ ∑ k ∈ s, b k ^ q * c ^ n := by
          gcongr with k hk
          rw [Complex.norm_real, Real.norm_of_nonneg (hv k).1]; exact (hv k).2
      _ ≤ 1 := hT
  have hbound3 := level_bound hc hq hqq hA h4 s b hb hT a L hL haL hab
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by rw [ENNReal.one_le_ofReal]; exact hq
  calc eLpNorm (cubeSum c s (fun k => (a k : ℂ) * (1 / (L : ℂ))) + cubeSum c s (fun k => (r k : ℂ))
        + cubeSum c s (fun k => (v k : ℂ))) (ENNReal.ofReal q) μ
      ≤ eLpNorm (cubeSum c s (fun k => (a k : ℂ) * (1 / (L : ℂ)))) (ENNReal.ofReal q)
          μ + eLpNorm (cubeSum c s (fun k => (r k : ℂ))) (ENNReal.ofReal q)
          μ + eLpNorm (cubeSum c s (fun k => (v k : ℂ))) (ENNReal.ofReal q)
          μ := by
        refine (eLpNorm_add_le ((aesm_cubeSum _ _ _).add (aesm_cubeSum _ _ _))
          (aesm_cubeSum _ _ _) hq1).trans ?_
        gcongr
        exact eLpNorm_add_le (aesm_cubeSum _ _ _) (aesm_cubeSum _ _ _) hq1
    _ ≤ ENNReal.ofReal (A / (1 - q / q₀)) +
          μ Set.univ ^ (ENNReal.ofReal q).toReal⁻¹ * ENNReal.ofReal 1 +
          μ Set.univ ^ (ENNReal.ofReal q).toReal⁻¹ * ENNReal.ofReal 1 := by
        gcongr
    _ = K2 μ q q₀ A := by
        rw [K2, ENNReal.ofReal_one, mul_one]; ring

/-- The bound for complex coefficients: `‖Σ a_k φ_k‖_{L^q(σ)} ≤ 4 K₂ (Σ |a_k|^q c^n)^{1/q}`. -/
lemma cube_bound (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℂ) :
    eLpNorm (cubeSum c s a) (ENNReal.ofReal q) μ ≤
      4 * K2 μ q q₀ A * ENNReal.ofReal ((∑ k ∈ s, ‖a k‖ ^ q * c ^ n) ^ (1 / q)) := by
  set T := ∑ k ∈ s, ‖a k‖ ^ q * c ^ n with hTdef
  have hq0 : 0 < q := by linarith
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun k _ => by positivity
  rcases hT0.eq_or_lt with hT | hT
  · -- all coefficients vanish
    have hz : ∀ k ∈ s, a k = 0 := by
      intro k hk
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).mp hT.symm k hk
      rcases mul_eq_zero.mp h with h | h
      · exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg _) hq0.ne').mp h)
      · exact absurd h (pow_ne_zero _ hc.ne')
    have : cubeSum c s a = 0 := by
      funext ω; simp only [cubeSum, Pi.zero_apply]
      exact Finset.sum_eq_zero fun k hk => by rw [hz k hk, zero_mul]
    rw [this, eLpNorm_zero]; exact bot_le
  · set lam := T ^ (1 / q) with hlam
    have hlam0 : 0 < lam := Real.rpow_pos_of_pos hT _
    have hlamq : lam ^ q = T := by
      rw [hlam, ← Real.rpow_mul hT.le, one_div_mul_cancel hq0.ne', Real.rpow_one]
    set b1 : (Fin n → ℤ) → ℝ := fun k => max (a k).re 0 / lam
    set b2 : (Fin n → ℤ) → ℝ := fun k => max (-(a k).re) 0 / lam
    set b3 : (Fin n → ℤ) → ℝ := fun k => max (a k).im 0 / lam
    set b4 : (Fin n → ℤ) → ℝ := fun k => max (-(a k).im) 0 / lam
    have hpos : ∀ (x : ℝ), 0 ≤ max x 0 / lam := fun x => div_nonneg (le_max_right _ _) hlam0.le
    have hsmall : ∀ (x : ℝ) (k : Fin n → ℤ), |x| ≤ ‖a k‖ →
        (max x 0 / lam) ^ q * c ^ n ≤ ‖a k‖ ^ q * c ^ n / T := by
      intro x k hx
      rw [div_eq_mul_inv (‖a k‖ ^ q * c ^ n), mul_right_comm]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [Real.div_rpow (le_max_right _ _) hlam0.le, hlamq, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Real.rpow_le_rpow (le_max_right _ _) _ hq0.le
      exact max_le (le_trans (le_abs_self x) hx) (norm_nonneg _)
    have hT1 : ∀ (x : (Fin n → ℤ) → ℝ), (∀ k, |x k| ≤ ‖a k‖) →
        ∑ k ∈ s, (max (x k) 0 / lam) ^ q * c ^ n ≤ 1 := by
      intro x hx
      calc ∑ k ∈ s, (max (x k) 0 / lam) ^ q * c ^ n ≤ ∑ k ∈ s, ‖a k‖ ^ q * c ^ n / T :=
            Finset.sum_le_sum fun k _ => hsmall (x k) k (hx k)
        _ = 1 := by rw [← Finset.sum_div, ← hTdef, div_self hT.ne']
    have hre : ∀ k, |(a k).re| ≤ ‖a k‖ := fun k => Complex.abs_re_le_norm _
    have him : ∀ k, |(a k).im| ≤ ‖a k‖ := fun k => Complex.abs_im_le_norm _
    have B1 := cube_bound_nonneg hc hq hqq hA h4 s b1 (fun k => hpos _) (hT1 _ hre)
    have B2 := cube_bound_nonneg hc hq hqq hA h4 s b2 (fun k => hpos _)
      (hT1 (fun k => -(a k).re) (fun k => by rw [abs_neg]; exact hre k))
    have B3 := cube_bound_nonneg hc hq hqq hA h4 s b3 (fun k => hpos _) (hT1 _ him)
    have B4 := cube_bound_nonneg hc hq hqq hA h4 s b4 (fun k => hpos _)
      (hT1 (fun k => -(a k).im) (fun k => by rw [abs_neg]; exact him k))
    have hdec : cubeSum c s a = (lam : ℂ) • (cubeSum c s (fun k => (b1 k : ℂ)) +
        (-1 : ℂ) • cubeSum c s (fun k => (b2 k : ℂ)) + Complex.I • cubeSum c s (fun k => (b3 k : ℂ))
        + (-Complex.I) • cubeSum c s (fun k => (b4 k : ℂ))) := by
      funext ω
      simp only [cubeSum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : a k = (lam : ℂ) * ((b1 k : ℂ) - b2 k + Complex.I * (b3 k - b4 k)) := by
        simp only [b1, b2, b3, b4]
        have e1 : max (a k).re 0 / lam - max (-(a k).re) 0 / lam = (a k).re / lam := by
          rw [← sub_div]; congr 1
          rcases le_total 0 (a k).re with h | h
          · rw [max_eq_left h, max_eq_right (by linarith)]; ring
          · rw [max_eq_right h, max_eq_left (by linarith)]; ring
        have e2 : max (a k).im 0 / lam - max (-(a k).im) 0 / lam = (a k).im / lam := by
          rw [← sub_div]; congr 1
          rcases le_total 0 (a k).im with h | h
          · rw [max_eq_left h, max_eq_right (by linarith)]; ring
          · rw [max_eq_right h, max_eq_left (by linarith)]; ring
        have : ((max (a k).re 0 / lam : ℝ) : ℂ) - ((max (-(a k).re) 0 / lam : ℝ) : ℂ) +
            Complex.I * (((max (a k).im 0 / lam : ℝ) : ℂ) - ((max (-(a k).im) 0 / lam : ℝ) : ℂ))
            = (((a k).re / lam : ℝ) : ℂ) + Complex.I * (((a k).im / lam : ℝ) : ℂ) := by
          rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, e1, e2]
        rw [this]
        apply Complex.ext <;> simp [hlam0.ne'] <;> field_simp
      rw [hk]; ring
    have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by rw [ENNReal.one_le_ofReal]; exact hq
    clear_value b1 b2 b3 b4
    rw [hdec, eLpNorm_const_smul]
    have hm : ∀ (z : ℂ), ‖z‖ₑ = 1 → ∀ (F : E n → ℂ),
        eLpNorm (z • F) (ENNReal.ofReal q) μ =
          eLpNorm F (ENNReal.ofReal q) μ := by
      intro z hz F; rw [eLpNorm_const_smul, hz, one_mul]
    have hlamE : ‖(lam : ℂ)‖ₑ = ENNReal.ofReal lam := by
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg hlam0.le]
    rw [hlamE, mul_comm (4 * K2 μ q q₀ A)]
    gcongr
    have a1 := aesm_cubeSum (μ := μ) c s (fun k => (b1 k : ℂ))
    have a2 := (aesm_cubeSum (μ := μ) c s (fun k => (b2 k : ℂ))).const_smul (-1 : ℂ)
    have a3 := (aesm_cubeSum (μ := μ) c s (fun k => (b3 k : ℂ))).const_smul Complex.I
    have a4 := (aesm_cubeSum (μ := μ) c s (fun k => (b4 k : ℂ))).const_smul (-Complex.I)
    have hI : ‖Complex.I‖ₑ = 1 := by
      rw [← ofReal_norm_eq_enorm, Complex.norm_I, ENNReal.ofReal_one]
    have hnI : ‖-Complex.I‖ₑ = 1 := by rw [enorm_neg, hI]
    have hn1 : ‖(-1 : ℂ)‖ₑ = 1 := by rw [enorm_neg, enorm_one]
    calc _ ≤ eLpNorm (cubeSum c s (fun k => (b1 k : ℂ))) (ENNReal.ofReal q) μ +
          eLpNorm ((-1 : ℂ) • cubeSum c s (fun k => (b2 k : ℂ))) (ENNReal.ofReal q)
            μ +
          eLpNorm (Complex.I • cubeSum c s (fun k => (b3 k : ℂ))) (ENNReal.ofReal q)
            μ +
          eLpNorm ((-Complex.I) • cubeSum c s (fun k => (b4 k : ℂ))) (ENNReal.ofReal q)
            μ := by
          refine (eLpNorm_add_le ((a1.add a2).add a3) a4 hq1).trans ?_
          gcongr ?_ + _
          refine (eLpNorm_add_le (a1.add a2) a3 hq1).trans ?_
          gcongr ?_ + _
          exact eLpNorm_add_le a1 a2 hq1
      _ = eLpNorm (cubeSum c s (fun k => (b1 k : ℂ))) (ENNReal.ofReal q) μ +
          eLpNorm (cubeSum c s (fun k => (b2 k : ℂ))) (ENNReal.ofReal q) μ +
          eLpNorm (cubeSum c s (fun k => (b3 k : ℂ))) (ENNReal.ofReal q) μ +
          eLpNorm (cubeSum c s (fun k => (b4 k : ℂ))) (ENNReal.ofReal q) μ := by
          rw [hm _ hn1, hm _ hI, hm _ hnI]
      _ ≤ K2 μ q q₀ A + K2 μ q q₀ A + K2 μ q q₀ A + K2 μ q q₀ A := by gcongr
      _ = 4 * K2 μ q q₀ A := by ring

end TaoBR.Tao49.PartC
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace
namespace TaoBR.Tao49.PartC
variable {n : ℕ}
/-- The unit box `[0, 1)ⁿ`. -/
def U (n : ℕ) : Set (E n) := {z | ∀ i, z i ∈ Set.Ico (0 : ℝ) 1}

lemma U_eq : U n = (WithLp.ofLp : E n → (Fin n → ℝ)) ⁻¹'
    Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1) := by
  ext z; simp [U]

lemma measurableSet_U : MeasurableSet (U n) := by
  rw [U_eq]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Ico).preimage (WithLp.measurable_ofLp 2 _)

lemma volume_U : volume (U n) = 1 := by
  rw [U_eq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    ((MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet), volume_pi,
    Measure.pi_pi]
  simp

/-- The lattice points in a box around `0`, enough to tile `closedBall 0 R`. -/
noncomputable def box (n : ℕ) (R : ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(⌈R⌉ + 1)) (⌈R⌉ + 1)

/-- The coordinatewise floor. -/
noncomputable def floorVec (x : E n) : Fin n → ℤ := fun i => ⌊x i⌋

lemma sub_latt_mem_U_iff (x : E n) (k : Fin n → ℤ) : x - latt k ∈ U n ↔ k = floorVec x := by
  simp only [U, Set.mem_setOf_eq, PiLp.sub_apply, latt_apply, Set.mem_Ico, sub_nonneg,
    floorVec]
  constructor
  · intro h; funext i
    show k i = ⌊x i⌋
    rw [eq_comm, Int.floor_eq_iff]; constructor <;> linarith [(h i).1, (h i).2]
  · intro h i
    rw [h]
    show (⌊x i⌋ : ℝ) ≤ x i ∧ x i - ⌊x i⌋ < 1
    exact ⟨Int.floor_le _, by linarith [Int.lt_floor_add_one (x i)]⟩

lemma floorVec_mem_box {R : ℝ} {x : E n} (hx : ‖x‖ ≤ R) : floorVec x ∈ box n R := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc, floorVec]
  intro i
  have h1 : |x i| ≤ R := by
    have := PiLp.norm_apply_le x i
    rw [Real.norm_eq_abs] at this; linarith
  have h2 := abs_le.mp h1
  have hc := Int.le_ceil R
  constructor
  · have : (-(⌈R⌉ + 1) : ℤ) < ⌊x i⌋ + 1 := by
      rw [← Int.cast_lt (R := ℝ)]; push_cast; linarith [Int.lt_floor_add_one (x i)]
    omega
  · have : (⌊x i⌋ : ℝ) ≤ ⌈R⌉ := by linarith [Int.floor_le (x i)]
    have : ⌊x i⌋ ≤ ⌈R⌉ := by exact_mod_cast this
    omega

/-- A function supported in `closedBall 0 R` is the sum of its pieces on the translated boxes. -/
lemma sum_indicator_tile {M : Type*} [AddCommMonoid M] {R : ℝ} (F : E n → M)
    (hF : ∀ x, F x ≠ 0 → ‖x‖ ≤ R) (x : E n) :
    ∑ k ∈ box n R, {y | y - latt k ∈ U n}.indicator F x = F x := by
  by_cases hx : F x = 0
  · rw [hx]; exact Finset.sum_eq_zero fun k _ => by
      by_cases h : x ∈ {y | y - latt k ∈ U n}
      · rw [Set.indicator_of_mem h, hx]
      · rw [Set.indicator_of_notMem h]
  · rw [Finset.sum_eq_single (floorVec x)]
    · rw [Set.indicator_of_mem]; exact (sub_latt_mem_U_iff x _).mpr rfl
    · intro k _ hk
      rw [Set.indicator_of_notMem]
      exact fun h => hk ((sub_latt_mem_U_iff x k).mp h)
    · intro h; exact absurd (floorVec_mem_box (hF x hx)) h

lemma tile_piece_indicator {M : Type*} [Zero M] (F : E n → M) (k : Fin n → ℤ) (z : E n) :
    {y | y - latt k ∈ U n}.indicator F (z + latt k) = (U n).indicator (fun z => F (z + latt k)) z := by
  by_cases h : z ∈ U n
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem]; simpa using h
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]; simpa using h

lemma measurableSet_tile (k : Fin n → ℤ) : MeasurableSet {y : E n | y - latt k ∈ U n} :=
  measurableSet_U.preimage (measurable_id.sub_const _)

lemma indicator_sum_comm {M : Type*} [AddCommMonoid M] (s : Finset (Fin n → ℤ))
    (G : (Fin n → ℤ) → E n → M) (z : E n) :
    ∑ k ∈ s, (U n).indicator (G k) z = (U n).indicator (fun z => ∑ k ∈ s, G k z) z := by
  by_cases h : z ∈ U n
  · simp only [Set.indicator_of_mem h]
  · simp only [Set.indicator_of_notMem h, Finset.sum_const_zero]

/-- Tiling for integrals. -/
lemma integral_tile {R : ℝ} (F : E n → ℂ) (hFi : Integrable F)
    (hF : ∀ x, F x ≠ 0 → ‖x‖ ≤ R) :
    ∫ x, F x = ∫ z, (U n).indicator (fun z => ∑ k ∈ box n R, F (z + latt k)) z := by
  calc ∫ x, F x = ∫ x, ∑ k ∈ box n R, {y | y - latt k ∈ U n}.indicator F x := by
        congr 1; funext x; rw [sum_indicator_tile F hF x]
    _ = ∑ k ∈ box n R, ∫ x, {y | y - latt k ∈ U n}.indicator F x := by
        rw [integral_finset_sum]
        exact fun k _ => hFi.indicator (measurableSet_tile k)
    _ = ∑ k ∈ box n R, ∫ z, (U n).indicator (fun z => F (z + latt k)) z := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← integral_add_right_eq_self (μ := (volume : Measure (E n))) _ (latt k)]
        congr 1; funext z; exact tile_piece_indicator F k z
    _ = ∫ z, ∑ k ∈ box n R, (U n).indicator (fun z => F (z + latt k)) z := by
        rw [integral_finset_sum]
        exact fun k _ => (hFi.comp_add_right (latt k)).indicator measurableSet_U
    _ = _ := by
        congr 1; funext z
        exact indicator_sum_comm _ _ _

/-- Tiling for lower integrals. -/
lemma lintegral_tile {R : ℝ} (F : E n → ℝ≥0∞) (hFm : Measurable F)
    (hF : ∀ x, F x ≠ 0 → ‖x‖ ≤ R) :
    ∫⁻ x, F x = ∫⁻ z in U n, ∑ k ∈ box n R, F (z + latt k) := by
  calc ∫⁻ x, F x = ∫⁻ x, ∑ k ∈ box n R, {y | y - latt k ∈ U n}.indicator F x := by
        congr 1; funext x; rw [sum_indicator_tile F hF x]
    _ = ∑ k ∈ box n R, ∫⁻ x, {y | y - latt k ∈ U n}.indicator F x := by
        rw [lintegral_finset_sum]
        exact fun k _ => hFm.indicator (measurableSet_tile k)
    _ = ∑ k ∈ box n R, ∫⁻ z, (U n).indicator (fun z => F (z + latt k)) z := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← lintegral_add_right_eq_self (μ := (volume : Measure (E n))) _ (latt k)]
        congr 1; funext z; exact tile_piece_indicator F k z
    _ = ∫⁻ z, ∑ k ∈ box n R, (U n).indicator (fun z => F (z + latt k)) z := by
        rw [lintegral_finset_sum]
        exact fun k _ => (hFm.comp (measurable_id.add_const _)).indicator measurableSet_U
    _ = _ := by
        rw [← lintegral_indicator measurableSet_U]
        congr 1; funext z
        exact indicator_sum_comm _ _ _

/-- The cube function with coefficients `f(z + k)`, evaluated at `ω`. -/
noncomputable def CPhi (c R : ℝ) (f : E n → ℂ) (z : E n) (ω : E n) : ℂ :=
  cubeSum c (box n R) (fun k => f (z + latt k)) ω

lemma continuous_CPhi (c R : ℝ) {f : E n → ℂ} (hf : Continuous f) :
    Continuous (fun p : E n × E n => CPhi c R f p.1 p.2) := by
  unfold CPhi cubeSum
  refine continuous_finset_sum _ fun k _ => ?_
  exact (hf.comp (continuous_fst.add continuous_const)).mul
    ((continuous_phi c k).comp continuous_snd)

lemma fourier_pointwise {c : ℝ} {m : ℝ} (hm0 : 0 < m) {R : ℝ} (f : E n → ℂ)
    (hfi : Integrable f) (hF : ∀ x, f x ≠ 0 → ‖x‖ ≤ R) (ω : E n) (hph : m ≤ ‖phi c 0 ω‖) :
    ‖𝓕 f ω‖ₑ ≤ ENNReal.ofReal m⁻¹ * ∫⁻ z in U n, ‖CPhi c R f z ω‖ₑ := by
  set F : E n → ℂ := fun x => 𝐞 (-⟪x, (ω : E n)⟫) • f x
  have hFi : Integrable F := (Real.fourierIntegral_convergent_iff (ω : E n)).2 hfi
  have hFs : ∀ x, F x ≠ 0 → ‖x‖ ≤ R := by
    intro x hx; apply hF x; intro h; apply hx; simp [F, h]
  have h1 : 𝓕 f ω = ∫ z, (U n).indicator (fun z => ∑ k ∈ box n R, F (z + latt k)) z := by
    rw [← integral_tile F hFi hFs]; exact fourier_eq f ω
  rw [h1]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  simp_rw [enorm_indicator_eq_indicator_enorm]
  rw [lintegral_indicator measurableSet_U, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun z => ?_
  set S : ℂ := ∑ k ∈ box n R, (𝐞 (-⟪latt k, (ω : E n)⟫) : ℂ) * f (z + latt k)
  have hsum : ∑ k ∈ box n R, F (z + latt k) = (𝐞 (-⟪z, (ω : E n)⟫) : ℂ) * S := by
    simp only [F, S, Finset.mul_sum, Circle.smul_def, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_add_left, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  have hPhi : CPhi c R f z ω = phi c 0 (ω : E n) * S := by
    simp only [CPhi, cubeSum, S, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [phi_translate, Circle.smul_def, smul_eq_mul]; ring
  rw [hsum, hPhi, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul
    (inv_nonneg.mpr hm0.le)]
  apply ENNReal.ofReal_le_ofReal
  rw [norm_mul, norm_mul, Circle.norm_coe, one_mul]
  rw [← mul_assoc, ← div_eq_inv_mul]
  have h1 : 1 ≤ ‖phi c 0 (ω : E n)‖ / m := by rw [le_div_iff₀ hm0]; linarith
  nlinarith [norm_nonneg S]

/-- Jensen on the unit box: `(∫_U |G|)^q ≤ ∫_U |G|^q`. -/
lemma jensen_U {q : ℝ} (hq : 1 ≤ q) (G : E n → ℂ) (hG : AEStronglyMeasurable G
    (volume.restrict (U n))) :
    (∫⁻ z in U n, ‖G z‖ₑ) ^ q ≤ ∫⁻ z in U n, ‖G z‖ₑ ^ q := by
  have hq0 : 0 < q := by linarith
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := ENNReal.ofReal q)
    (by rw [ENNReal.one_le_ofReal]; exact hq) hG
  rw [Measure.restrict_apply_univ, volume_U, ENNReal.one_rpow, mul_one,
    eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le] at h
  calc (∫⁻ z in U n, ‖G z‖ₑ) ^ q ≤ ((∫⁻ z in U n, ‖G z‖ₑ ^ q) ^ (1 / q)) ^ q :=
        ENNReal.rpow_le_rpow h hq0.le
    _ = _ := by rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]

end TaoBR.Tao49.PartC
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace
namespace TaoBR.Tao49.PartC
variable {n : ℕ} {μ : Measure (E n)} [IsFiniteMeasure μ]
variable {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {q q₀ A : ℝ} (hq : 1 ≤ q) (hqq : q < q₀) (hA : 0 ≤ A)
  (h4 : ∀ t : Finset (Fin n → ℤ), eLpNorm (cubeSum c t (fun _ => 1)) (ENNReal.ofReal q)
      μ ≤ ENNReal.ofReal (A * ((t.card : ℝ) * c ^ n) ^ (1 / q₀)))
include hc hq hqq hA h4
lemma Phi_lintegral_le (R : ℝ) (f : E n → ℂ) (z : E n) :
    ∫⁻ ω, ‖CPhi c R f z ω‖ₑ ^ q ∂μ ≤
      (4 * K2 μ q q₀ A) ^ q * (ENNReal.ofReal (c ^ n) *
        ∑ k ∈ box n R, ‖f (z + latt k)‖ₑ ^ q) := by
  have hq0 : 0 < q := by linarith
  have hb := cube_bound hc hq hqq hA h4 (box n R) (fun k => f (z + latt k))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le] at hb
  have hb' := ENNReal.rpow_le_rpow hb hq0.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le, ← Real.rpow_mul (by positivity),
    one_div_mul_cancel hq0.ne', Real.rpow_one] at hb'
  refine hb'.trans (le_of_eq ?_)
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ENNReal.ofReal_mul (by positivity), mul_comm,
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le, ofReal_norm_eq_enorm]

lemma fourier_eLpNorm_le {m : ℝ} (hm0 : 0 < m)
    (hm : ∀ᵐ ω ∂μ, m ≤ ‖phi c 0 ω‖) {R : ℝ} (f : E n → ℂ) (hf : Continuous f)
    (hfi : Integrable f) (hF : ∀ x, f x ≠ 0 → ‖x‖ ≤ R) :
    eLpNorm (𝓕 f) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal m⁻¹ * (4 * K2 μ q q₀ A) * ENNReal.ofReal (c ^ n) ^ (1 / q) *
        eLpNorm f (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le]
  have hmeas : Measurable (fun p : E n × E n => ‖CPhi c R f p.1 p.2‖ₑ ^ q) :=
    ((continuous_CPhi c R hf).measurable.enorm).pow_const _
  have key : ∫⁻ ω, ‖𝓕 f ω‖ₑ ^ q ∂μ ≤
      (ENNReal.ofReal m⁻¹ * (4 * K2 μ q q₀ A)) ^ q * (ENNReal.ofReal (c ^ n) * ∫⁻ x, ‖f x‖ₑ ^ q) := by
    calc ∫⁻ ω, ‖𝓕 f ω‖ₑ ^ q ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal m⁻¹ ^ q * ((∫⁻ z in U n, ‖CPhi c R f z ω‖ₑ) ^ q)
            ∂μ := by
          refine lintegral_mono_ae (hm.mono fun ω hω => ?_)
          rw [← ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
          exact ENNReal.rpow_le_rpow (fourier_pointwise hm0 f hfi hF ω hω) hq0.le
      _ ≤ ∫⁻ ω, ENNReal.ofReal m⁻¹ ^ q * (∫⁻ z in U n, ‖CPhi c R f z ω‖ₑ ^ q)
            ∂μ := by
          refine lintegral_mono fun ω => ?_
          gcongr
          exact jensen_U hq _ ((continuous_CPhi c R hf).comp
            (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      _ = ENNReal.ofReal m⁻¹ ^ q * ∫⁻ z in U n, (∫⁻ ω, ‖CPhi c R f z ω‖ₑ ^ q
            ∂μ) := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top),
            lintegral_lintegral_swap]
          exact (hmeas.comp measurable_swap).aemeasurable
      _ ≤ ENNReal.ofReal m⁻¹ ^ q * ∫⁻ z in U n, (4 * K2 μ q q₀ A) ^ q *
            (ENNReal.ofReal (c ^ n) * ∑ k ∈ box n R, ‖f (z + latt k)‖ₑ ^ q) := by
          gcongr with z
          exact Phi_lintegral_le hc hq hqq hA h4 R f z
      _ = ENNReal.ofReal m⁻¹ ^ q * ((4 * K2 μ q q₀ A) ^ q * (ENNReal.ofReal (c ^ n) *
            ∫⁻ z in U n, ∑ k ∈ box n R, ‖f (z + latt k)‖ₑ ^ q)) := by
          rw [lintegral_const_mul' _ _ ?_, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine ENNReal.rpow_ne_top_of_nonneg hq0.le ?_
          refine ENNReal.mul_ne_top (by simp) ?_
          simp only [K2]
          refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) ?_, ENNReal.ofReal_ne_top⟩
          exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)
      _ = (ENNReal.ofReal m⁻¹ * (4 * K2 μ q q₀ A)) ^ q * (ENNReal.ofReal (c ^ n) * ∫⁻ x, ‖f x‖ₑ ^ q) := by
          rw [← lintegral_tile (R := R) (fun x => ‖f x‖ₑ ^ q)
            (hf.measurable.enorm.pow_const _)]
          · rw [ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal m⁻¹) (4 * K2 μ q q₀ A) hq0.le]; ring
          · intro x hx; apply hF x; intro h; apply hx; simp [h, hq0]
  calc (∫⁻ ω, ‖𝓕 f ω‖ₑ ^ q ∂μ) ^ (1 / q)
      ≤ ((ENNReal.ofReal m⁻¹ * (4 * K2 μ q q₀ A)) ^ q * (ENNReal.ofReal (c ^ n) * ∫⁻ x, ‖f x‖ₑ ^ q)) ^ (1 / q) :=
        ENNReal.rpow_le_rpow key (by positivity)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg ((ENNReal.ofReal m⁻¹ * (4 * K2 μ q q₀ A)) ^ q) _
            (by positivity),
          ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal (c ^ n)) _ (by positivity),
          ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
        ring

end TaoBR.Tao49.PartC
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace SchwartzMap
namespace TaoBR.Tao49.PartC
/-- **G3 (the p. 7 reduction, `c = 1/2`).** A bound for indicators of unions of `1/2`-cubes gives
`R_μ(q, 0)` for every `q < q₀`. -/
theorem restrMu_zero_of_cubeUnion_bound {n : ℕ} (hn : 2 ≤ n) {μ : Measure (E n)} {S : Set (E n)}
    (hμ : DecayMeasure μ S) (p : ℝ) (q₀ : ℝ) (hq₀ : 1 < q₀) (hq₀p : q₀ ≤ p)
    (h : ∃ C : ℝ, ∀ T : Set (E n), IsCubeUnion (1 / 2) T →
      eLpNorm (𝓕 (T.indicator fun _ => (1 : ℂ))) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C * (volume T).toReal ^ (1 / q₀))) :
    ∀ q : ℝ, 1 ≤ q → q < q₀ → RestrMu μ q 0 := by
  haveI := hμ.finite
  intro qr hqr1 hqrq
  obtain ⟨C, hC⟩ := h
  set c : ℝ := 1 / 2 with hcdef
  have hc : 0 < c := by norm_num [hcdef]
  have hc1 : c < 1 := by norm_num [hcdef]
  have hqr0 : 0 < qr := by linarith
  set σu := μ Set.univ with hσu
  have hσtop : σu ≠ ⊤ := measure_ne_top _ _
  set e := 1 / qr - 1 / p with he
  have he0 : 0 ≤ e := by
    rw [he, sub_nonneg]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
  set A := max C 0 * σu.toReal ^ e with hAdef
  have hA : 0 ≤ A := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have h4 : ∀ t : Finset (Fin n → ℤ), eLpNorm (cubeSum c t (fun _ => 1)) (ENNReal.ofReal qr)
      μ ≤ ENNReal.ofReal (A * ((t.card : ℝ) * c ^ n) ^ (1 / q₀)) := by
    intro t
    have h1 := hC (⋃ k ∈ t, cCube c k) ⟨t, rfl⟩
    rw [restriction_iUnion hc1 t, volume_iUnion_cCube hc.le hc1 t] at h1
    have hV : ((t.card : ℝ≥0∞) * ENNReal.ofReal c ^ n).toReal = (t.card : ℝ) * c ^ n := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hc.le]; simp
    rw [hV] at h1
    have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ)
      (p := ENNReal.ofReal qr) (q := ENNReal.ofReal p)
      (ENNReal.ofReal_le_ofReal (by linarith)) (aesm_cubeSum c t (fun _ => 1))
    rw [ENNReal.toReal_ofReal hqr0.le, ENNReal.toReal_ofReal (by linarith)] at h2
    refine h2.trans ?_
    have hσe : σu ^ (1 / qr - 1 / p) = ENNReal.ofReal (σu.toReal ^ e) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg he0, ENNReal.ofReal_toReal hσtop]
    rw [← hσu, hσe]
    calc eLpNorm (cubeSum c t fun _ => 1) (ENNReal.ofReal p) μ *
          ENNReal.ofReal (σu.toReal ^ e)
        ≤ ENNReal.ofReal (max C 0 * ((t.card : ℝ) * c ^ n) ^ (1 / q₀)) *
          ENNReal.ofReal (σu.toReal ^ e) := by
          gcongr
          refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
          gcongr; exact le_max_left _ _
      _ = ENNReal.ofReal (A * ((t.card : ℝ) * c ^ n) ^ (1 / q₀)) := by
          rw [← ENNReal.ofReal_mul (by positivity), hAdef]; ring_nf
  obtain ⟨m, hm0, hm⟩ := exists_lower_bound_phi (n := n) (r := 3 / 2) hc (by norm_num [hcdef])
  have hSae : ∀ᵐ ω ∂μ, ω ∈ S := mem_ae_iff.mpr hμ.null_compl
  have hmae : ∀ᵐ ω ∂μ, m ≤ ‖phi c 0 ω‖ :=
    hSae.mono fun ω hω => hm ω (mem_closedBall_zero_iff.mp (hμ.subset hω))
  set Kc : ℝ≥0∞ := ENNReal.ofReal m⁻¹ * (4 * K2 μ qr q₀ A) * ENNReal.ofReal (c ^ n) ^ (1 / qr)
  have hKc : Kc ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (by simp) ?_)) (ENNReal.rpow_ne_top_of_nonneg (by positivity)
        ENNReal.ofReal_ne_top)
    simp only [K2]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) ?_, ENNReal.ofReal_ne_top⟩
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hσtop
  refine ⟨Kc.toNNReal, fun R hR f hf => ?_⟩
  rw [Real.rpow_zero, ENNReal.ofReal_one, mul_one, ENNReal.coe_toNNReal hKc]
  refine fourier_eLpNorm_le hc hqr1 hqrq hA h4 hm0 hmae (R := R) f f.continuous f.integrable ?_
  intro x hx
  have := hf (subset_tsupport _ (Function.mem_support.mpr hx))
  rwa [mem_closedBall_zero_iff] at this

end TaoBR.Tao49.PartC
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
alias restrMu_zero_of_cubeUnion_bound := TaoBR.Tao49.PartC.restrMu_zero_of_cubeUnion_bound

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open MeasureTheory Metric
open scoped FourierTransform ENNReal NNReal SchwartzMap ContDiff RealInnerProductSpace
namespace TaoBR.Tao49.PartD
variable {n : ℕ}
/-!
# Part D of the Theorem 4.9 Blueprint (port of `proofs/parab/PartD.lean`)
-/
/-- The indicator of a set, with value `1 : ℂ`. -/
noncomputable def chi (G : Set (E n)) : E n → ℂ := G.indicator fun _ => (1 : ℂ)

lemma unique_ball {M : ℕ} {x : Fin M → E n} {R : ℝ}
    (hsep : ∀ i j, i ≠ j → 4 * R ≤ dist (x i) (x j)) {y : E n} {i j : Fin M}
    (hi : y ∈ ball (x i) (2 * R)) (hj : y ∈ ball (x j) (2 * R)) : i = j := by
  by_contra h
  have := hsep i j h
  rw [mem_ball] at hi hj
  have := dist_triangle_left (x i) (x j) y
  linarith

/-- A smooth cutoff: `1` on the `R`-balls, supported in the `2R`-balls. -/
lemma exists_cutoff {M : ℕ} (x : Fin M → E n) {R : ℝ} (hR : 0 < R)
    (hsep : ∀ i j, i ≠ j → 4 * R ≤ dist (x i) (x j)) :
    ∃ θ : E n → ℝ, ContDiff ℝ ∞ θ ∧ (∀ y, 0 ≤ θ y ∧ θ y ≤ 1) ∧
      (∀ y ∈ ⋃ i, closedBall (x i) R, θ y = 1) ∧
      tsupport θ ⊆ ⋃ i, closedBall (x i) (2 * R) := by
  let b : ∀ i, ContDiffBump (x i) := fun i => ⟨R, 2 * R, hR, by linarith⟩
  refine ⟨fun y => ∑ i, b i y, ?_, ?_, ?_, ?_⟩
  · exact ContDiff.sum fun i _ => (b i).contDiff
  · intro y
    dsimp only
    by_cases h : ∃ i, y ∈ ball (x i) (2 * R)
    · obtain ⟨i, hi⟩ := h
      rw [Finset.sum_eq_single i]
      · exact ⟨(b i).nonneg, (b i).le_one⟩
      · intro j _ hj
        apply (b j).zero_of_le_dist
        by_contra hlt; push_neg at hlt
        exact hj (unique_ball hsep (by simpa [mem_ball] using hlt) hi)
      · simp
    · push_neg at h
      rw [Finset.sum_eq_zero fun j _ => (b j).zero_of_le_dist (by
        have := h j; rw [mem_ball] at this; push_neg at this; exact this)]
      simp
  · intro y hy
    dsimp only
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    rw [Finset.sum_eq_single i]
    · exact (b i).one_of_mem_closedBall hi
    · intro j _ hj
      apply (b j).zero_of_le_dist
      by_contra hlt; push_neg at hlt
      have hi' : y ∈ ball (x i) (2 * R) := by
        rw [mem_closedBall] at hi; rw [mem_ball]; linarith
      exact hj (unique_ball hsep (by simpa [mem_ball] using hlt) hi')
    · simp
  · apply closure_minimal _ (isClosed_iUnion_of_finite fun i => isClosed_closedBall)
    intro y hy
    rw [Function.mem_support] at hy
    obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    have : y ∈ Function.support (b i) := hi
    rw [(b i).support_eq] at this
    exact Set.mem_iUnion.mpr ⟨i, ball_subset_closedBall this⟩

lemma measure_iUnion_closedBall_lt_top {M : ℕ} (x : Fin M → E n) (r : ℝ) :
    volume (⋃ i, closedBall (x i) r) < ⊤ :=
  (measure_iUnion_fintype_le _ _).trans_lt
    (ENNReal.sum_lt_top.mpr fun i _ => measure_closedBall_lt_top)

/-- Schwartz approximation of an indicator, supported in the doubled balls. -/
lemma exists_schwartz_approx {M : ℕ} (x : Fin M → E n) {R : ℝ} (hR : 0 < R)
    (hsep : ∀ i j, i ≠ j → 4 * R ≤ dist (x i) (x j)) {G : Set (E n)} (hG : MeasurableSet G)
    (hGsub : G ⊆ ⋃ i, closedBall (x i) R) {q : ℝ} (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : 𝓢(E n, ℂ), tsupport f ⊆ ⋃ i, closedBall (x i) (2 * R) ∧
      eLpNorm (fun y => f y - chi G y) (ENNReal.ofReal q) volume ≤ ENNReal.ofReal ε ∧
      ∫⁻ y, ‖f y - chi G y‖ₑ ≤ ENNReal.ofReal ε := by
  obtain ⟨θ, hθs, hθ01, hθ1, hθsupp⟩ := exists_cutoff x hR hsep
  set K₂ := ⋃ i, closedBall (x i) (2 * R)
  have hK₂m : MeasurableSet K₂ := MeasurableSet.iUnion fun i => measurableSet_closedBall
  set V := volume K₂ with hV
  have hVtop : V ≠ ⊤ := (measure_iUnion_closedBall_lt_top x _).ne
  have hq0 : 0 < q := by linarith
  set e : ℝ := 1 - 1 / q
  have he0 : 0 ≤ e := by simp only [e]; rw [sub_nonneg, div_le_one hq0]; exact hq
  set ε₁ : ℝ := ε / (1 + V.toReal ^ e)
  have hε₁ : 0 < ε₁ := div_pos hε (by positivity)
  have hGfin : volume G < ⊤ := (measure_mono hGsub).trans_lt
    (measure_iUnion_closedBall_lt_top x R)
  have hmem : MemLp (chi G) (ENNReal.ofReal q) volume :=
    memLp_indicator_const _ hG _ (Or.inr hGfin.ne)
  obtain ⟨g, hgc, hgs, hgε⟩ := MeasureTheory.MemLp.exist_eLpNorm_sub_le ENNReal.ofReal_ne_top
    (by rw [ENNReal.one_le_ofReal]; exact hq) hmem hε₁
  set F : E n → ℂ := fun y => (θ y : ℂ) * g y
  have hFs : ContDiff ℝ ∞ F := (Complex.ofRealCLM.contDiff.comp hθs).mul hgs
  have hFc : HasCompactSupport F := hgc.mul_left
  let f : 𝓢(E n, ℂ) := hFc.toSchwartzMap hFs
  have hfF : ∀ y, f y = F y := fun y => rfl
  have hdiff : ∀ y, f y - chi G y = (θ y : ℂ) * (g y - chi G y) := by
    intro y
    rw [hfF]
    by_cases hy : y ∈ G
    · simp [F, chi, hy, hθ1 y (hGsub hy)]
    · simp [F, chi, hy]
  have hpt : ∀ y, ‖f y - chi G y‖ₑ ≤ ‖(chi G - g) y‖ₑ := by
    intro y
    rw [hdiff, enorm_mul, Pi.sub_apply, ← enorm_neg (chi G y - g y), neg_sub]
    calc ‖(θ y : ℂ)‖ₑ * ‖g y - chi G y‖ₑ ≤ 1 * ‖g y - chi G y‖ₑ := by
          gcongr
          rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hθ01 y).1]
          simpa using (hθ01 y).2
      _ = _ := one_mul _
  have hLq : eLpNorm (fun y => f y - chi G y) (ENNReal.ofReal q) volume ≤ ENNReal.ofReal ε₁ :=
    (eLpNorm_mono_enorm hpt).trans hgε
  have hsupp : Function.support (fun y => f y - chi G y) ⊆ K₂ := by
    intro y hy
    rw [Function.mem_support, hdiff] at hy
    have : θ y ≠ 0 := fun h => hy (by simp [h])
    exact hθsupp (subset_tsupport _ this)
  refine ⟨f, ?_, hLq.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · exact (closure_mono (fun y hy => by
      rw [Function.mem_support, hfF] at hy
      exact fun h => hy (by simp [F, h]))).trans hθsupp
  · exact div_le_self hε.le (le_add_of_nonneg_right (by positivity))
  · -- `L¹` on the bounded set `K₂`
    have hrest : eLpNorm (fun y => f y - chi G y) 1 volume =
        eLpNorm (fun y => f y - chi G y) 1 (volume.restrict K₂) :=
      (eLpNorm_restrict_eq_of_support_subset hsupp).symm
    have hrestq : eLpNorm (fun y => f y - chi G y) (ENNReal.ofReal q) (volume.restrict K₂) =
        eLpNorm (fun y => f y - chi G y) (ENNReal.ofReal q) volume :=
      eLpNorm_restrict_eq_of_support_subset hsupp
    have hm : AEStronglyMeasurable (fun y => f y - chi G y) (volume.restrict K₂) :=
      (f.continuous.aestronglyMeasurable.sub
        ((aestronglyMeasurable_const.indicator hG))).restrict
    have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict K₂) (p := 1)
      (q := ENNReal.ofReal q) (by rw [ENNReal.one_le_ofReal]; exact hq) hm
    rw [← hrest, hrestq, Measure.restrict_apply_univ, ENNReal.toReal_one,
      ENNReal.toReal_ofReal hq0.le, eLpNorm_one_eq_lintegral_enorm] at h1
    refine h1.trans ?_
    calc eLpNorm (fun y => f y - chi G y) (ENNReal.ofReal q) volume * V ^ (1 / 1 - 1 / q)
        ≤ ENNReal.ofReal ε₁ * ENNReal.ofReal (V.toReal ^ e) := by
          gcongr
          rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg he0,
            ENNReal.ofReal_toReal hVtop]
          simp [e]
      _ = ENNReal.ofReal (ε₁ * V.toReal ^ e) := (ENNReal.ofReal_mul hε₁.le).symm
      _ ≤ ENNReal.ofReal ε := by
          apply ENNReal.ofReal_le_ofReal
          simp only [ε₁]
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [show 0 ≤ V.toReal ^ e by positivity]

lemma enorm_fourier_sub_le {f g : E n → ℂ} (hf : Integrable f) (hg : Integrable g)
    (ξ : E n) :
    ‖𝓕 f ξ - 𝓕 g ξ‖ₑ ≤ ∫⁻ y, ‖f y - g y‖ₑ := by
  simp only [Real.fourier_eq]
  rw [← integral_sub ((Real.fourierIntegral_convergent_iff _).2 hf)
    ((Real.fourierIntegral_convergent_iff _).2 hg)]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1; funext y
  rw [← smul_sub, Circle.smul_def, enorm_smul, ← ofReal_norm (𝐞 _ : ℂ), Circle.norm_coe,
    ENNReal.ofReal_one, one_mul]

lemma continuous_fourier_of_integrable {f : E n → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar
    (by simpa using (continuous_inner : Continuous fun p : E n × E n => ⟪p.1, p.2⟫)) hf

lemma integrable_chi {G : Set (E n)} (hG : MeasurableSet G) (hfin : volume G < ⊤) :
    Integrable (chi G) :=
  (integrableOn_const hfin.ne).integrable_indicator hG

/-- The Schwartz bound on the doubled balls passes to indicators of subsets of the balls. -/
lemma fourier_chi_le {μ : Measure (E n)} [IsFiniteMeasure μ] {M : ℕ} (x : Fin M → E n) {R : ℝ}
    (hR : 0 < R)
    (hsep : ∀ i j, i ≠ j → 4 * R ≤ dist (x i) (x j)) {G : Set (E n)} (hG : MeasurableSet G)
    (hGsub : G ⊆ ⋃ i, closedBall (x i) R) {q : ℝ} (hq : 1 ≤ q) {K : ℝ≥0∞} (hKtop : K ≠ ⊤)
    (hK : ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ ⋃ i, closedBall (x i) (2 * R) →
      eLpNorm (𝓕 (f : E n → ℂ)) (ENNReal.ofReal q) μ ≤
        K * eLpNorm f (ENNReal.ofReal q) volume) :
    eLpNorm (𝓕 (chi G)) (ENNReal.ofReal q) μ ≤
      K * eLpNorm (chi G) (ENNReal.ofReal q) volume := by
  have hGfin : volume G < ⊤ := (measure_mono hGsub).trans_lt
    (measure_iUnion_closedBall_lt_top x R)
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by rw [ENNReal.one_le_ofReal]; exact hq
  set Ms : ℝ≥0∞ := μ Set.univ ^ (ENNReal.ofReal q).toReal⁻¹
  have hMs : Ms ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set δ : ℝ := ε / (K.toReal + Ms.toReal + 1)
  have hδ : 0 < δ := div_pos (by exact_mod_cast hε) (by positivity)
  obtain ⟨f, hfs, hLq, hL1⟩ := exists_schwartz_approx x hR hsep hG hGsub hq hδ
  have hdiff : ∀ ξ, ‖𝓕 (chi G) ξ - 𝓕 (f : E n → ℂ) ξ‖ ≤ δ := by
    intro ξ
    have h := enorm_fourier_sub_le (integrable_chi hG hGfin) f.integrable ξ
    have h2 : ∫⁻ y, ‖chi G y - f y‖ₑ = ∫⁻ y, ‖f y - chi G y‖ₑ := by
      congr 1; funext y; rw [← enorm_neg, neg_sub]
    rw [h2] at h
    have := h.trans hL1
    rw [← ofReal_norm] at this
    exact (ENNReal.ofReal_le_ofReal_iff hδ.le).mp this
  have hsplit : 𝓕 (chi G) =
      𝓕 (f : E n → ℂ) + (𝓕 (chi G) - 𝓕 (f : E n → ℂ)) := by abel
  have hcf := (continuous_fourier_of_integrable f.integrable).aestronglyMeasurable (μ := μ)
  have hcg := (continuous_fourier_of_integrable (integrable_chi hG hGfin)).aestronglyMeasurable
    (μ := μ)
  have hfχ : eLpNorm (⇑f) (ENNReal.ofReal q) volume ≤
      eLpNorm (chi G) (ENNReal.ofReal q) volume + ENNReal.ofReal δ := by
    have : (⇑f) = chi G + (fun y => f y - chi G y) := by funext y; simp
    rw [this]
    refine (eLpNorm_add_le ?_ ?_ hq1).trans (by gcongr)
    · exact (aestronglyMeasurable_const.indicator hG)
    · exact f.continuous.aestronglyMeasurable.sub (aestronglyMeasurable_const.indicator hG)
  calc eLpNorm (𝓕 (chi G)) (ENNReal.ofReal q) μ
      ≤ eLpNorm (𝓕 (f : E n → ℂ)) (ENNReal.ofReal q) μ +
        eLpNorm (𝓕 (chi G) - 𝓕 (f : E n → ℂ)) (ENNReal.ofReal q) μ := by
        conv_lhs => rw [hsplit]
        exact eLpNorm_add_le hcf (hcg.sub hcf) hq1
    _ ≤ K * (eLpNorm (chi G) (ENNReal.ofReal q) volume + ENNReal.ofReal δ) +
        Ms * ENNReal.ofReal δ := by
        gcongr
        · exact (hK f hfs).trans (by gcongr)
        · exact eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall hdiff)
    _ = K * eLpNorm (chi G) (ENNReal.ofReal q) volume + (K + Ms) * ENNReal.ofReal δ := by ring
    _ ≤ K * eLpNorm (chi G) (ENNReal.ofReal q) volume + ε := by
        gcongr
        rw [← ENNReal.ofReal_toReal hKtop, ← ENNReal.ofReal_toReal hMs,
          ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal]
        apply ENNReal.ofReal_le_ofReal
        simp only [δ]
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ ε := ε.2
        nlinarith

/-! ### Disjointifying a finite cover -/
/-- The `k`-th set of a finite family, as an `ℕ`-indexed sequence (empty past the end). -/
def ext {J : ℕ} (B : Fin J → Set (E n)) (k : ℕ) : Set (E n) :=
  if h : k < J then B ⟨k, h⟩ else ∅

lemma chi_eq_sum {J : ℕ} (B : Fin J → Set (E n)) {S : Set (E n)} (hS : S ⊆ ⋃ j, B j)
    (y : E n) :
    chi S y = ∑ k ∈ Finset.range J, chi (S ∩ disjointed (ext B) k) y := by
  by_cases hy : y ∈ S
  · have hU : y ∈ ⋃ k, disjointed (ext B) k := by
      rw [iUnion_disjointed]
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hS hy)
      exact Set.mem_iUnion.mpr ⟨j, by simp [ext, j.2, hj]⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hU
    have hkJ : k < J := by
      by_contra h
      have := disjointed_subset (ext B) k hk
      simp [ext, h] at this
    rw [Finset.sum_eq_single k]
    · simp [chi, hy, hk]
    · intro l _ hl
      have : y ∉ disjointed (ext B) l := fun h =>
        Set.disjoint_left.mp (disjoint_disjointed (ext B) hl) h hk
      simp [chi, this]
    · intro h; exact absurd (Finset.mem_range.mpr hkJ) h
  · rw [Finset.sum_eq_zero]
    · simp [chi, hy]
    · intro k _; simp [chi, hy]

lemma fourier_finset_sum {ι : Type*} (s : Finset ι) (F : ι → E n → ℂ)
    (hF : ∀ i ∈ s, Integrable (F i)) :
    𝓕 (fun y => ∑ i ∈ s, F i y) = fun ξ => ∑ i ∈ s, 𝓕 (F i) ξ := by
  funext ξ
  simp only [Real.fourier_eq, Finset.smul_sum]
  exact integral_finsetSum s fun i hi => (Real.fourierIntegral_convergent_iff _).2 (hF i hi)

/-! ### Cubes -/
/-- The `c`-cube as a box of `Fin n → ℝ`. -/
lemma cCube_eq (c : ℝ) (k : Fin n → ℤ) :
    cCube c k = (WithLp.ofLp : E n → (Fin n → ℝ)) ⁻¹'
      Set.pi Set.univ (fun i => Set.Icc ((k i : ℝ) - c / 2) (k i + c / 2)) := by
  ext x
  simp only [cCube, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  show (∀ i, |x i - k i| ≤ c / 2) ↔ _
  constructor
  · intro h i; have := abs_le.mp (h i); exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · intro h i; have := h i; exact abs_le.mpr ⟨by linarith [this.1], by linarith [this.2]⟩

lemma measurableSet_cCube (c : ℝ) (k : Fin n → ℤ) : MeasurableSet (cCube c k) := by
  rw [cCube_eq]
  exact (MeasurableSet.univ_pi fun i => measurableSet_Icc).preimage
    (WithLp.measurable_ofLp 2 _)

lemma volume_cCube {c : ℝ} (hc : 0 ≤ c) (k : Fin n → ℤ) :
    volume (cCube c k) = ENNReal.ofReal c ^ n := by
  rw [cCube_eq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    ((MeasurableSet.univ_pi fun i => measurableSet_Icc).nullMeasurableSet), volume_pi,
    Measure.pi_pi]
  have : ∀ i : Fin n, ((k i : ℝ) + c / 2 - (k i - c / 2)) = c := fun i => by ring
  simp only [Real.volume_Icc, this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma volume_cCube_lt_top (c : ℝ) (k : Fin n → ℤ) : volume (cCube c k) < ⊤ := by
  have hsub : cCube c k ⊆ cCube |c| k := fun x hx i => (hx i).trans (by
    have := le_abs_self c; linarith)
  calc volume (cCube c k) ≤ volume (cCube |c| k) := measure_mono hsub
    _ < ⊤ := by rw [volume_cCube (abs_nonneg c)]; exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

lemma sparse_double {M : ℕ} {x : Fin M → E n} {C₀ R : ℝ} (hR : 1 ≤ R)
    (h : IsSparse (2 * max C₀ 2) R x) :
    IsSparse C₀ (2 * R) x ∧ ∀ i j, i ≠ j → 4 * R ≤ dist (x i) (x j) := by
  set C := max C₀ 2
  have hC2 : (2 : ℝ) ≤ C := le_max_right _ _
  have hC0 : C₀ ≤ C := le_max_left _ _
  have key : ∀ i j, i ≠ j → (2 * R) ^ C * (M : ℝ) ^ C ≤ dist (x i) (x j) := by
    intro i j hij
    have hM : (2 : ℝ) ≤ M := by
      have : (2 : ℕ) ≤ M := by
        have := i.2; have := j.2; have : i.val ≠ j.val := fun e => hij (Fin.ext e); omega
      exact_mod_cast this
    have hM1 : (1 : ℝ) ≤ M := by linarith
    have hRC : 1 ≤ R ^ C := Real.one_le_rpow hR (by linarith)
    have hMC : 1 ≤ (M : ℝ) ^ C := Real.one_le_rpow hM1 (by linarith)
    have h2M : (2 : ℝ) ^ C ≤ (M : ℝ) ^ C := Real.rpow_le_rpow (by norm_num) hM (by linarith)
    calc (2 * R) ^ C * (M : ℝ) ^ C = 2 ^ C * R ^ C * (M : ℝ) ^ C := by
          rw [Real.mul_rpow (by norm_num) (by linarith)]
      _ ≤ (M : ℝ) ^ C * R ^ C * (M : ℝ) ^ C := by gcongr
      _ = (R ^ C * ((M : ℝ) ^ C * (M : ℝ) ^ C)) * 1 := by ring
      _ ≤ (R ^ C * ((M : ℝ) ^ C * (M : ℝ) ^ C)) * R ^ C :=
          mul_le_mul_of_nonneg_left hRC (by positivity)
      _ = (R ^ C * R ^ C) * ((M : ℝ) ^ C * (M : ℝ) ^ C) := by ring
      _ = R ^ (2 * C) * (M : ℝ) ^ (2 * C) := by
          rw [two_mul, Real.rpow_add (by linarith), Real.rpow_add (by linarith)]
      _ ≤ dist (x i) (x j) := h i j hij
  constructor
  · intro i j hij
    refine le_trans ?_ (key i j hij)
    have hM1 : (1 : ℝ) ≤ M := by
      have : (1 : ℕ) ≤ M := Nat.one_le_iff_ne_zero.mpr (fun h0 => by subst h0; exact i.elim0)
      exact_mod_cast this
    exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by linarith) hC0)
      (Real.rpow_le_rpow_of_exponent_le hM1 hC0) (by positivity) (by positivity)
  · intro i j hij
    refine le_trans ?_ (key i j hij)
    have hM1 : (1 : ℝ) ≤ M := by
      have : (1 : ℕ) ≤ M := Nat.one_le_iff_ne_zero.mpr (fun h0 => by subst h0; exact i.elim0)
      exact_mod_cast this
    have h1 : (2 * R) ^ (2 : ℝ) ≤ (2 * R) ^ C := Real.rpow_le_rpow_of_exponent_le (by linarith) hC2
    have h2 : 1 ≤ (M : ℝ) ^ C := Real.one_le_rpow hM1 (by linarith)
    rw [Real.rpow_two] at h1
    nlinarith

lemma volume_cubeUnion_lt_top {c : ℝ} {S : Set (E n)} (hS : IsCubeUnion c S) : volume S < ⊤ := by
  obtain ⟨s, rfl⟩ := hS
  exact (measure_biUnion_finset_le _ _).trans_lt
    (ENNReal.sum_lt_top.mpr fun k _ => volume_cCube_lt_top c k)

lemma measurableSet_cubeUnion {c : ℝ} {S : Set (E n)} (hS : IsCubeUnion c S) :
    MeasurableSet S := by
  obtain ⟨s, rfl⟩ := hS
  exact Finset.measurableSet_biUnion _ fun k _ => measurableSet_cCube c k

/-- The bound (4) for one union of cubes, from a sparse cover and the sparse estimate. -/
lemma cube_bound_from_cover {μ : Measure (E n)} [IsFiniteMeasure μ] {p : ℝ} (hp : 1 ≤ p)
    {α : ℝ} (hα : 0 < α) {C₀ : ℝ} {C : ℝ≥0}
    (hU : ∀ R : ℝ, 1 ≤ R → ∀ (N : ℕ) (x : Fin N → E n), IsSparse C₀ R x →
      ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ ⋃ i, closedBall (x i) R →
        eLpNorm (𝓕 (f : E n → ℂ)) (ENNReal.ofReal p) μ ≤
          C * ENNReal.ofReal (R ^ α) * eLpNorm f (ENNReal.ofReal p) volume)
    {S : Set (E n)} (hSm : MeasurableSet S) (hSfin : volume S < ⊤)
    {J : ℕ} {R : Fin J → ℝ} {M : Fin J → ℕ} {x : (j : Fin J) → Fin (M j) → E n}
    {Rmax : ℝ} (hR : ∀ j, 1 ≤ R j ∧ R j ≤ Rmax ∧ IsSparse (2 * max C₀ 2) (R j) (x j))
    (hcov : S ⊆ ⋃ (j) (i), closedBall (x j i) (R j)) :
    eLpNorm (𝓕 (chi S)) (ENNReal.ofReal p) μ ≤
      J * (C * ENNReal.ofReal ((2 * Rmax) ^ α) * volume S ^ (1 / p)) := by
  set B : Fin J → Set (E n) := fun j => ⋃ i, closedBall (x j i) (R j)
  set G : ℕ → Set (E n) := fun k => S ∩ disjointed (ext B) k
  have hBm : ∀ k, MeasurableSet (ext B k) := by
    intro k; unfold ext; split_ifs
    · exact MeasurableSet.iUnion fun i => measurableSet_closedBall
    · exact MeasurableSet.empty
  have hGm : ∀ k, MeasurableSet (G k) := fun k => hSm.inter (MeasurableSet.disjointed hBm k)
  have hGfin : ∀ k, volume (G k) < ⊤ := fun k =>
    (measure_mono Set.inter_subset_left).trans_lt hSfin
  have hS' : S ⊆ ⋃ j, B j := by
    intro y hy
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov hy)
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  have hsum : 𝓕 (chi S) = ∑ k ∈ Finset.range J, 𝓕 (chi (G k)) := by
    have : chi S = fun y => ∑ k ∈ Finset.range J, chi (G k) y := funext (chi_eq_sum B hS')
    rw [this, fourier_finset_sum _ _ fun k _ => integrable_chi (hGm k) (hGfin k)]
    funext ξ; simp [Finset.sum_apply]
  rw [hsum]
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by rw [ENNReal.one_le_ofReal]; exact hp
  refine (eLpNorm_sum_le (fun k _ =>
    (continuous_fourier_of_integrable
      (integrable_chi (hGm k) (hGfin k))).aestronglyMeasurable) hp1).trans ?_
  have hterm : ∀ k ∈ Finset.range J, eLpNorm (𝓕 (chi (G k))) (ENNReal.ofReal p) μ ≤
      C * ENNReal.ofReal ((2 * Rmax) ^ α) * volume S ^ (1 / p) := by
    intro k hk
    have hkJ := Finset.mem_range.mp hk
    set j : Fin J := ⟨k, hkJ⟩
    obtain ⟨hR1, hRle, hsp⟩ := hR j
    obtain ⟨hsp2, hsep⟩ := sparse_double hR1 hsp
    have hGsub : G k ⊆ ⋃ i, closedBall (x j i) (R j) := by
      intro y hy
      have := disjointed_subset (ext B) k hy.2
      simpa [ext, hkJ, B, j] using this
    have hK : ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ ⋃ i, closedBall (x j i) (2 * R j) →
        eLpNorm (𝓕 (f : E n → ℂ)) (ENNReal.ofReal p) μ ≤
          (C * ENNReal.ofReal ((2 * R j) ^ α)) * eLpNorm f (ENNReal.ofReal p) volume :=
      fun f hf => hU (2 * R j) (by linarith) (M j) (x j) hsp2 f hf
    have h1 := fourier_chi_le (μ := μ) (x j) (by linarith) hsep (hGm k) hGsub hp
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hK
    refine h1.trans ?_
    have hchi : eLpNorm (chi (G k)) (ENNReal.ofReal p) volume ≤ volume S ^ (1 / p) := by
      unfold chi
      rw [eLpNorm_indicator_const (hGm k) (by simp; linarith) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (by linarith)]
      simp only [enorm_one, one_mul]
      exact ENNReal.rpow_le_rpow (measure_mono Set.inter_subset_left) (by positivity)
    have hRR : ENNReal.ofReal ((2 * R j) ^ α) ≤ ENNReal.ofReal ((2 * Rmax) ^ α) :=
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by linarith) (by linarith) hα.le)
    exact mul_le_mul' (mul_le_mul' le_rfl hRR) hchi
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The choice `N ≈ log(1/α) / (2 log C₁)`. -/
lemma key_N {C₁ L : ℝ} (hC₁ : 2 ≤ C₁) (hL : 4 * Real.log (4 * C₁) < L) :
    ∃ N : ℕ, 1 ≤ N ∧ 1 / (N : ℝ) + Real.exp (-L) * C₁ ^ N ≤ (2 * Real.log C₁ + 1) / L := by
  have hlc : 0 < Real.log C₁ := Real.log_pos (by linarith)
  have h4 : 0 < Real.log (4 * C₁) := Real.log_pos (by linarith)
  have hL0 : 0 < L := by linarith
  set N := ⌈L / (2 * Real.log C₁)⌉₊
  have hpos : 0 < L / (2 * Real.log C₁) := by positivity
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hpos).ne'
  have hNge : L / (2 * Real.log C₁) ≤ N := Nat.le_ceil _
  have hNlt : (N : ℝ) < L / (2 * Real.log C₁) + 1 := Nat.ceil_lt_add_one hpos.le
  refine ⟨N, hN1, ?_⟩
  have h1 : 1 / (N : ℝ) ≤ 2 * Real.log C₁ / L := by
    rw [div_le_div_iff₀ (by positivity) hL0]
    rw [div_le_iff₀ (by positivity)] at hNge
    linarith
  have hpow : C₁ ^ N = Real.exp (N * Real.log C₁) := by
    rw [← Real.exp_log (show 0 < C₁ by linarith), ← Real.exp_nat_mul, Real.log_exp]
  have h2 : Real.exp (-L) * C₁ ^ N ≤ 1 / L := by
    rw [hpow, ← Real.exp_add]
    have hlt : -L + N * Real.log C₁ ≤ -L / 2 + Real.log C₁ := by
      have : (N : ℝ) * Real.log C₁ ≤ (L / (2 * Real.log C₁) + 1) * Real.log C₁ :=
        mul_le_mul_of_nonneg_right hNlt.le hlc.le
      rw [add_mul, div_mul_eq_mul_div, mul_div_assoc, mul_comm 2 (Real.log C₁),
        div_mul_cancel_left₀ hlc.ne'] at this
      linarith
    refine (Real.exp_le_exp.mpr hlt).trans ?_
    rw [Real.exp_add, Real.exp_log (by linarith), le_div_iff₀ hL0]
    -- `L C₁ ≤ exp(L/2)`
    have hq : 4 * C₁ < Real.exp (L / 4) := by
      rw [← Real.exp_log (show 0 < 4 * C₁ by linarith)]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hq2 : L / 4 ≤ Real.exp (L / 4) := by linarith [Real.add_one_le_exp (L / 4)]
    have hsq : Real.exp (L / 2) = Real.exp (L / 4) * Real.exp (L / 4) := by
      rw [← Real.exp_add]; ring_nf
    have hneg : Real.exp (-L / 2) * Real.exp (L / 2) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    have key : L * C₁ ≤ Real.exp (L / 2) := by
      rw [hsq]; nlinarith [Real.exp_pos (L / 4)]
    have hE := Real.exp_pos (-L / 2)
    calc Real.exp (-L / 2) * C₁ * L = Real.exp (-L / 2) * (L * C₁) := by ring
      _ ≤ Real.exp (-L / 2) * Real.exp (L / 2) := mul_le_mul_of_nonneg_left key hE.le
      _ = 1 := hneg
  calc 1 / (N : ℝ) + Real.exp (-L) * C₁ ^ N ≤ 2 * Real.log C₁ / L + 1 / L := add_le_add h1 h2
    _ = _ := by ring

/-- The numerical bound behind (4). -/
lemma numeric {A C α m N p r c0 s : ℝ} (hA : 1 ≤ A) (hC : 0 ≤ C) (hα : 0 < α) (hm : 0 ≤ m)
    (hN : 1 ≤ N) (hp : 0 < p) (hr : 1 / p ≤ r) (hexp : 1 / N + α * m + 1 / p ≤ r)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hs : s = 0 ∨ c0 ≤ s) :
    A * N * s ^ (1 / N) * (C * (2 * (A * (max 1 s) ^ m)) ^ α * s ^ (1 / p)) ≤
      (A * N * C * (2 * A) ^ α * c0 ^ (1 / p - r)) * s ^ r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hK0 : 0 ≤ A * N * C * (2 * A) ^ α := by positivity
  have hcz : 1 ≤ c0 ^ (1 / p - r) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hc0 hc01 (by linarith)
  rcases hs with hs | hs
  · subst hs
    rw [Real.zero_rpow (by positivity), Real.zero_rpow hr0.ne']; simp
  have hs0 : 0 < s := lt_of_lt_of_le hc0 hs
  have hsplit : (2 * (A * (max 1 s) ^ m)) ^ α = (2 * A) ^ α * (max 1 s) ^ (m * α) := by
    rw [← mul_assoc, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
  rw [hsplit]
  rcases le_total 1 s with h1 | h1
  · rw [max_eq_right h1]
    have : s ^ (1 / N) * (s ^ (m * α) * s ^ (1 / p)) = s ^ (1 / N + α * m + 1 / p) := by
      rw [← Real.rpow_add hs0, ← Real.rpow_add hs0]; ring_nf
    calc A * N * s ^ (1 / N) * (C * ((2 * A) ^ α * s ^ (m * α)) * s ^ (1 / p))
        = (A * N * C * (2 * A) ^ α) * (s ^ (1 / N) * (s ^ (m * α) * s ^ (1 / p))) := by ring
      _ = (A * N * C * (2 * A) ^ α) * s ^ (1 / N + α * m + 1 / p) := by rw [this]
      _ ≤ (A * N * C * (2 * A) ^ α) * s ^ r :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 hexp) hK0
      _ ≤ (A * N * C * (2 * A) ^ α * c0 ^ (1 / p - r)) * s ^ r := by
          exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hK0 hcz) (by positivity)
  · rw [max_eq_left h1, Real.one_rpow, mul_one]
    have hsN : s ^ (1 / N) ≤ 1 := Real.rpow_le_one hs0.le h1 (by positivity)
    have hsp : s ^ (1 / p) = s ^ r * s ^ (1 / p - r) := by
      rw [← Real.rpow_add hs0]; ring_nf
    have hsc : s ^ (1 / p - r) ≤ c0 ^ (1 / p - r) :=
      Real.rpow_le_rpow_of_nonpos hc0 hs (by linarith)
    calc A * N * s ^ (1 / N) * (C * (2 * A) ^ α * s ^ (1 / p))
        = (A * N * C * (2 * A) ^ α) * s ^ (1 / N) * s ^ (1 / p) := by ring
      _ ≤ (A * N * C * (2 * A) ^ α) * 1 * s ^ (1 / p) := by gcongr
      _ = (A * N * C * (2 * A) ^ α) * (s ^ r * s ^ (1 / p - r)) := by rw [hsp]; ring
      _ ≤ (A * N * C * (2 * A) ^ α) * (s ^ r * c0 ^ (1 / p - r)) := by gcongr
      _ = _ := by ring

lemma cubeUnion_volume_cases {S : Set (E n)} (hS : IsCubeUnion (1 / 2) S) :
    (volume S).toReal = 0 ∨ (1 / 2 : ℝ) ^ n ≤ (volume S).toReal := by
  obtain ⟨s, rfl⟩ := hS
  rcases s.eq_empty_or_nonempty with h | ⟨k, hk⟩
  · left; subst h; simp
  · right
    have hle : volume (cCube (1 / 2) k) ≤ volume (⋃ k ∈ s, cCube (1 / 2 : ℝ) k) :=
      measure_mono (Set.subset_biUnion_of_mem (u := fun k => cCube (1 / 2 : ℝ) k) hk)
    rw [volume_cCube (by norm_num)] at hle
    have := ENNReal.toReal_mono (volume_cubeUnion_lt_top ⟨s, rfl⟩).ne hle
    rwa [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num)] at this

/-- **G4 (Theorem 1.2).** `κ` and `α₀` do not depend on `p` (they come from the separation exponent
of `top_L2` and from `exists_sparse_cover`), which is what lets the assembly send `p ↑ p_c`. -/
theorem restrMu_zero_of_restrMu {n : ℕ} (hn : 2 ≤ n) {μ : Measure (E n)} {S : Set (E n)}
    (hμ : DecayMeasure μ S) :
    ∃ κ α₀ : ℝ, 0 < α₀ ∧ ∀ p : ℝ, 1 < p → p < 2 → ∀ α : ℝ, 0 < α → α < α₀ →
      RestrMu μ p α → ∀ q : ℝ, 1 ≤ q → 1 / p + κ / Real.log (1 / α) < 1 / q →
        RestrMu μ q 0 := by
  have := hμ.finite
  obtain ⟨C0, hC0, A2, hA2, hL2⟩ := top_L2w hn hμ
  obtain ⟨A, C₁, hcov⟩ := exists_sparse_cover n hn (1 / 2) (by norm_num) (2 * max (C0 : ℝ) 2)
  set A' := max A 1
  set C₁' := max |C₁| 2
  have hA' : 1 ≤ A' := le_max_right _ _
  have hC₁' : 2 ≤ C₁' := le_max_right _ _
  set κ := 2 * Real.log C₁' + 1
  set α₀ := min (1 / 2) (Real.exp (-(4 * Real.log (4 * C₁'))))
  refine ⟨κ, α₀, lt_min (by norm_num) (Real.exp_pos _), ?_⟩
  intro p hp hp2 α hα hαα hT q hq hqr
  have hp0 : 0 < p := by linarith
  have hα1 : α < 1 := lt_of_lt_of_le hαα ((min_le_left _ _).trans (by norm_num))
  set L := Real.log (1 / α)
  have hLeq : L = -Real.log α := by simp [L, Real.log_inv]
  have hLbig : 4 * Real.log (4 * C₁') < L := by
    rw [hLeq]
    have := Real.log_lt_log hα (lt_of_lt_of_le hαα (min_le_right _ _))
    rw [Real.log_exp] at this; linarith
  have hL0 : 0 < L := lt_of_le_of_lt (by
    have := Real.log_pos (show (1 : ℝ) < 4 * C₁' by linarith); linarith) hLbig
  have hαexp : α = Real.exp (-L) := by rw [hLeq, neg_neg, Real.exp_log hα]
  obtain ⟨N, hN1, hNkey⟩ := key_N hC₁' hLbig
  obtain ⟨C, hC⟩ := sparse_of_restrMu hn hμ hC0 hA2 hL2 hp hp2 hα.le hT
  set r := 1 / p + κ / L
  have hr1 : r < 1 := by
    by_contra h
    push_neg at h
    have : 1 / q ≤ 1 := by rw [div_le_one (by linarith)]; exact hq
    linarith
  have hrp : 1 / p ≤ r := by
    have : 0 ≤ κ / L := div_nonneg (by
      have := Real.log_pos (show (1:ℝ) < C₁' by linarith); linarith) hL0.le
    simp only [r]; linarith
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hrp
  set q₀ := 1 / r
  have hq₀ : 1 < q₀ := by rw [lt_one_div (by norm_num) hr0]; simpa using hr1
  have hq₀p : q₀ ≤ p := by
    simp only [q₀]; rw [div_le_iff₀ hr0]
    rw [div_le_iff₀ hp0] at hrp; linarith
  have hqq₀ : q < q₀ := by
    simp only [q₀]; rw [lt_div_iff₀ hr0]
    rw [lt_div_iff₀ (by linarith)] at hqr; linarith
  have hexp : 1 / (N : ℝ) + α * C₁' ^ N + 1 / p ≤ r := by
    simp only [r]; rw [hαexp]; linarith
  set c0 : ℝ := (1 / 2) ^ n
  set Cα : ℝ := A' * N * C * (2 * A') ^ α * c0 ^ (1 / p - r)
  refine restrMu_zero_of_cubeUnion_bound hn hμ p q₀ hq₀ hq₀p ⟨Cα, fun S hS => ?_⟩ q hq hqq₀
  -- the bound (4) for `S`
  have hSfin := volume_cubeUnion_lt_top hS
  set s := (volume S).toReal
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  obtain ⟨J, R, M, x, hJ, hRb, hScov⟩ := hcov S hS N hN1
  set Rmax := A' * (max 1 s) ^ (C₁' ^ N)
  have hRb' : ∀ j, 1 ≤ R j ∧ R j ≤ Rmax ∧ IsSparse (2 * max (C0 : ℝ) 2) (R j) (x j) := by
    intro j
    obtain ⟨h1, h2, h3⟩ := hRb j
    refine ⟨h1, h2.trans ?_, h3⟩
    have hu : 1 ≤ max 1 s := le_max_left _ _
    have hab : |C₁| ^ N ≤ C₁' ^ N := pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) N
    have hpow : C₁ ^ N ≤ C₁' ^ N := by
      have := le_abs_self (C₁ ^ N)
      rw [abs_pow] at this
      linarith
    calc A * max 1 s ^ C₁ ^ N ≤ A' * max 1 s ^ C₁ ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ A' * max 1 s ^ C₁' ^ N := by
          gcongr
  have hmain := cube_bound_from_cover (μ := μ) hp.le hα hC (measurableSet_cubeUnion hS) hSfin
    hRb' hScov
  have hchi : chi S = S.indicator fun _ => (1 : ℂ) := rfl
  rw [← hchi]
  refine hmain.trans ?_
  have hJ' : (J : ℝ≥0∞) ≤ ENNReal.ofReal (A' * N * s ^ (1 / (N : ℝ))) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hJ.trans (by gcongr; exact le_max_left _ _))
  have hvol : volume S ^ (1 / p) = ENNReal.ofReal (s ^ (1 / p)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hs0 (by positivity), ENNReal.ofReal_toReal hSfin.ne]
  have hRpos : 0 ≤ Rmax := by positivity
  calc (J : ℝ≥0∞) * (C * ENNReal.ofReal ((2 * Rmax) ^ α) * volume S ^ (1 / p))
      ≤ ENNReal.ofReal (A' * N * s ^ (1 / (N : ℝ))) *
          (ENNReal.ofReal C * ENNReal.ofReal ((2 * Rmax) ^ α) * ENNReal.ofReal (s ^ (1 / p))) := by
        rw [hvol, ENNReal.ofReal_coe_nnreal]; gcongr
    _ = ENNReal.ofReal (A' * N * s ^ (1 / (N : ℝ)) *
          (C * (2 * Rmax) ^ α * s ^ (1 / p))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (Cα * s ^ (1 / q₀)) := by
        apply ENNReal.ofReal_le_ofReal
        have h1q : 1 / q₀ = r := by simp [q₀]
        rw [h1q]
        exact numeric hA' C.2 hα (by positivity) (by exact_mod_cast hN1) hp0 hrp hexp
          (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
          (cubeUnion_volume_cases hS)

end TaoBR.Tao49.PartD
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
alias restrMu_zero_of_restrMu := TaoBR.Tao49.PartD.restrMu_zero_of_restrMu

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartI1
/-!
# Part I1 of the Theorem 4.9 Blueprint: `interp_L1_Lp`

Real interpolation between `L¹` and `L^{p₀}` (Marcinkiewicz), as `marc` in
`proofs/parab/PartB.lean` with `p₀` in place of `2`: the layer-cake formula and the split
`g = g 1_{|g| > t} + g 1_{|g| ≤ t}` give, when both bounds hold with the same constant `A`,
`∫ |T g|^r ≤ r (2/(r-1) + 2^{p₀}/(p₀-r)) A ∫ |g|^r`; apply it to `λ T` with
`λ = (A₁/A₀)^{1/(p₀-1)}` (so that `λ A₁ = λ^{p₀} A₀`) and divide by `λ^r`.

No Blueprint definitions are needed.
-/
noncomputable def truncHi {X : Type*} (g : X → ℂ) (t : ℝ) : X → ℂ :=
  fun x => if t < ‖g x‖ then g x else 0

noncomputable def truncLo {X : Type*} (g : X → ℂ) (t : ℝ) : X → ℂ :=
  fun x => if t < ‖g x‖ then 0 else g x

lemma truncHi_add_truncLo {X : Type*} (g : X → ℂ) (t : ℝ) :
    truncHi g t + truncLo g t = g := by
  funext x
  simp only [truncHi, truncLo, Pi.add_apply]
  split_ifs <;> simp

lemma enorm_truncHi {X : Type*} (g : X → ℂ) (t : ℝ) (x : X) :
    ‖truncHi g t x‖ₑ = if t < ‖g x‖ then ENNReal.ofReal ‖g x‖ else 0 := by
  simp only [truncHi]; split_ifs <;> simp

lemma enorm_truncLo_rpow {X : Type*} (g : X → ℂ) (t : ℝ) {p₀ : ℝ} (hp₀ : 0 < p₀) (x : X) :
    ‖truncLo g t x‖ₑ ^ p₀ = if t < ‖g x‖ then 0 else ENNReal.ofReal (‖g x‖ ^ p₀) := by
  simp only [truncLo]; split_ifs
  · simp [ENNReal.zero_rpow_of_pos hp₀]
  · rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp₀.le]

/-- `∫_0^s t^(r-2) dt = s^(r-1)/(r-1)`. -/
lemma lint_low {q : ℝ} (hq1 : 1 < q) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ t in Ioo 0 s, ENNReal.ofReal (t ^ (q - 2)) = ENNReal.ofReal (s ^ (q - 1) / (q - 1)) := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (q - 2)) volume 0 s :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hio : IntegrableOn (fun t : ℝ => t ^ (q - 2)) (Ioo 0 s) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hs).1 hint).mono_set Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hio]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs,
      integral_rpow (Or.inl (by linarith))]
    rw [show q - 2 + 1 = q - 1 by ring, Real.zero_rpow (by linarith)]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _

/-- `∫_s^∞ t^(r-p₀-1) dt = s^(r-p₀)/(p₀-r)`. -/
lemma lint_high {r p₀ : ℝ} (hrp : r < p₀) {s : ℝ} (hs : 0 < s) :
    ∫⁻ t in Ioi s, ENNReal.ofReal (t ^ (r - p₀ - 1)) =
      ENNReal.ofReal (s ^ (r - p₀) / (p₀ - r)) := by
  have hio : IntegrableOn (fun t : ℝ => t ^ (r - p₀ - 1)) (Ioi s) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hs
  rw [← ofReal_integral_eq_lintegral_ofReal hio]
  · congr 1
    rw [integral_Ioi_rpow_of_lt (by linarith) hs, show r - p₀ - 1 + 1 = r - p₀ by ring]
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hs.trans ht).le _

/-- The per-point one-dimensional computation. -/
lemma lint_point {p₀ r : ℝ} (hr1 : 1 < r) (hrp : r < p₀) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ t in Ioi 0, (ENNReal.ofReal (2 / t) * (if t < s then ENNReal.ofReal s else 0) +
        ENNReal.ofReal ((2 / t) ^ p₀) * (if t < s then 0 else ENNReal.ofReal (s ^ p₀))) *
        ENNReal.ofReal (t ^ (r - 1)) ≤
      ENNReal.ofReal ((2 / (r - 1) + 2 ^ p₀ / (p₀ - r)) * s ^ r) := by
  have hp0 : 0 < p₀ := by linarith
  rcases hs.eq_or_lt with hs0 | hs0
  · subst hs0
    have : ∀ t ∈ Ioi (0 : ℝ), (ENNReal.ofReal (2 / t) * (if t < 0 then ENNReal.ofReal 0 else 0) +
        ENNReal.ofReal ((2 / t) ^ p₀) * (if t < 0 then 0 else ENNReal.ofReal ((0 : ℝ) ^ p₀))) *
        ENNReal.ofReal (t ^ (r - 1)) = 0 := by
      intro t ht; simp [Real.zero_rpow hp0.ne']
    rw [setLIntegral_congr_fun measurableSet_Ioi this]; simp
  have e1 : ∀ t ∈ Ioi (0 : ℝ), (ENNReal.ofReal (2 / t) * (if t < s then ENNReal.ofReal s else 0) +
        ENNReal.ofReal ((2 / t) ^ p₀) * (if t < s then 0 else ENNReal.ofReal (s ^ p₀))) *
        ENNReal.ofReal (t ^ (r - 1)) =
      (Iio s).indicator (fun t => ENNReal.ofReal (2 * s) * ENNReal.ofReal (t ^ (r - 2))) t +
      (Ici s).indicator (fun t => ENNReal.ofReal (2 ^ p₀ * s ^ p₀) *
        ENNReal.ofReal (t ^ (r - p₀ - 1))) t := by
    intro t ht
    have ht : 0 < t := ht
    have r1 : t ^ (r - 1) = t ^ (r - 2) * t := by
      rw [← Real.rpow_add_one ht.ne']; ring_nf
    have r2 : t ^ (r - 1) = t ^ (r - p₀ - 1) * t ^ p₀ := by
      rw [← Real.rpow_add ht]; ring_nf
    have r3 : (2 / t) ^ p₀ = 2 ^ p₀ / t ^ p₀ := Real.div_rpow (by norm_num) ht.le _
    have htp : 0 < t ^ p₀ := Real.rpow_pos_of_pos ht _
    by_cases h : t < s
    · have h' : t ∉ Ici s := by simpa using h
      rw [if_pos h, if_pos h, indicator_of_mem (show t ∈ Iio s from h), indicator_of_notMem h',
        mul_zero, add_zero, add_zero, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1; rw [r1]; field_simp
    · have h' : t ∈ Ici s := by simpa using h
      rw [if_neg h, if_neg h, indicator_of_notMem (show t ∉ Iio s from h), indicator_of_mem h',
        mul_zero, zero_add, zero_add, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1; rw [r2, r3]; field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi e1]
  rw [lintegral_add_left]
  swap
  · exact Measurable.indicator (by fun_prop) measurableSet_Iio
  rw [lintegral_indicator measurableSet_Iio, lintegral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Iio, Measure.restrict_restrict measurableSet_Ici,
    lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop)]
  have i1 : Iio s ∩ Ioi 0 = Ioo 0 s := by ext; simp [and_comm]
  have i2 : Ici s ∩ Ioi (0 : ℝ) = Ici s := inter_eq_left.2 (fun t ht => hs0.trans_le ht)
  rw [i1, i2, setLIntegral_congr Ioi_ae_eq_Ici.symm, lint_low hr1 hs, lint_high hrp hs0,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply le_of_eq; congr 1
  have a1 : s * s ^ (r - 1) = s ^ r := by
    rw [← Real.rpow_one_add' hs0.le (by linarith)]; ring_nf
  have a2 : s ^ p₀ * s ^ (r - p₀) = s ^ r := by
    rw [← Real.rpow_add hs0]; ring_nf
  have hq1' : r - 1 ≠ 0 := by linarith
  have hq2' : p₀ - r ≠ 0 := by linarith
  calc 2 * s * (s ^ (r - 1) / (r - 1)) + 2 ^ p₀ * s ^ p₀ * (s ^ (r - p₀) / (p₀ - r))
      = 2 * (s * s ^ (r - 1)) / (r - 1) + 2 ^ p₀ * (s ^ p₀ * s ^ (r - p₀)) / (p₀ - r) := by
        ring
    _ = _ := by rw [a1, a2]; ring

end TaoBR.Tao49.PartI1
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartI1
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (P : (X → ℂ) → Prop)
    (T : (X → ℂ) → Y → ℂ) (A : ℝ≥0∞)
omit [SFinite μ] [SFinite ν] in
include P in
lemma marc_step
    (hPhi : ∀ g t, P g → P (truncHi g t)) (hPlo : ∀ g t, P g → P (truncLo g t))
    (hlin : ∀ g g', P g → P g' → T (g + g') = T g + T g')
    (hmeasT : ∀ g, P g → Measurable (T g)) {p₀ : ℝ} (hp₀ : 0 < p₀)
    (h1 : ∀ g, P g → ∫⁻ y, ‖T g y‖ₑ ∂ν ≤ A * ∫⁻ x, ‖g x‖ₑ ∂μ)
    (h0 : ∀ g, P g → ∫⁻ y, ‖T g y‖ₑ ^ p₀ ∂ν ≤ A * ∫⁻ x, ‖g x‖ₑ ^ p₀ ∂μ)
    (g : X → ℂ) (hg : P g) (t : ℝ) (ht : 0 < t) :
    ν {y | t < ‖T g y‖} ≤
      A * (ENNReal.ofReal (2 / t) * (∫⁻ x, ‖truncHi g t x‖ₑ ∂μ) +
        ENNReal.ofReal ((2 / t) ^ p₀) * (∫⁻ x, ‖truncLo g t x‖ₑ ^ p₀ ∂μ)) := by
  have hsplit : T g = T (truncHi g t) + T (truncLo g t) := by
    rw [← hlin _ _ (hPhi g t hg) (hPlo g t hg), truncHi_add_truncLo]
  have hsub : {y | t < ‖T g y‖} ⊆ {y | t / 2 ≤ ‖T (truncHi g t) y‖} ∪
      {y | t / 2 ≤ ‖T (truncLo g t) y‖} := by
    intro y hy
    simp only [mem_ofPred_eq, mem_union] at hy ⊢
    by_contra hc
    push Not at hc
    rw [hsplit, Pi.add_apply] at hy
    linarith [norm_add_le (T (truncHi g t) y) (T (truncLo g t) y)]
  have c1 : ν {y | t / 2 ≤ ‖T (truncHi g t) y‖} ≤
      ENNReal.ofReal (2 / t) * (A * (∫⁻ x, ‖truncHi g t x‖ₑ ∂μ)) := by
    have hm := (hmeasT _ (hPhi g t hg)).enorm.aemeasurable (μ := ν)
    have := mul_meas_ge_le_lintegral₀ hm (ENNReal.ofReal (t / 2))
    have hset : {y | ENNReal.ofReal (t / 2) ≤ ‖T (truncHi g t) y‖ₑ} =
        {y | t / 2 ≤ ‖T (truncHi g t) y‖} := by
      ext y; simp only [mem_ofPred_eq, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)
    rw [hset] at this
    have hpos : ENNReal.ofReal (t / 2) ≠ 0 := by simpa using ht
    have e2 : ENNReal.ofReal (2 / t) = (ENNReal.ofReal (t / 2))⁻¹ := by
      rw [← ENNReal.ofReal_inv_of_pos (by positivity)]; congr 1; field_simp
    rw [e2, ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hpos)
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact this.trans (h1 _ (hPhi g t hg))
  have c2 : ν {y | t / 2 ≤ ‖T (truncLo g t) y‖} ≤
      ENNReal.ofReal ((2 / t) ^ p₀) * (A * (∫⁻ x, ‖truncLo g t x‖ₑ ^ p₀ ∂μ)) := by
    have hm := ((hmeasT _ (hPlo g t hg)).enorm.pow_const p₀).aemeasurable (μ := ν)
    have := mul_meas_ge_le_lintegral₀ hm (ENNReal.ofReal ((t / 2) ^ p₀))
    have hset : {y | ENNReal.ofReal ((t / 2) ^ p₀) ≤ ‖T (truncLo g t) y‖ₑ ^ p₀} =
        {y | t / 2 ≤ ‖T (truncLo g t) y‖} := by
      ext y; simp only [mem_ofPred_eq, ← ofReal_norm]
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp₀.le,
        ENNReal.ofReal_le_ofReal_iff (by positivity)]
      exact Real.rpow_le_rpow_iff (by positivity) (norm_nonneg _) hp₀
    rw [hset] at this
    have hpos : ENNReal.ofReal ((t / 2) ^ p₀) ≠ 0 := by
      have : 0 < (t / 2) ^ p₀ := Real.rpow_pos_of_pos (by positivity) _
      simpa using this
    have e2 : ENNReal.ofReal ((2 / t) ^ p₀) = (ENNReal.ofReal ((t / 2) ^ p₀))⁻¹ := by
      rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
      congr 1
      rw [← Real.inv_rpow (by positivity), inv_div]
    rw [e2, ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hpos)
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact this.trans (h0 _ (hPlo g t hg))
  calc ν {y | t < ‖T g y‖} ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add c1 c2
    _ = _ := by ring

/-- The integrand after the layer-cake step. -/
noncomputable def marcF (g : X → ℂ) (p₀ r : ℝ) (t : ℝ) (x : X) : ℝ≥0∞ :=
  (ENNReal.ofReal (2 / t) * (if t < ‖g x‖ then ENNReal.ofReal ‖g x‖ else 0) +
    ENNReal.ofReal ((2 / t) ^ p₀) * (if t < ‖g x‖ then 0 else ENNReal.ofReal (‖g x‖ ^ p₀))) *
    ENNReal.ofReal (t ^ (r - 1))

omit [MeasurableSpace Y] in
lemma marcF_meas (g : X → ℂ) (hg : Measurable g) (p₀ r : ℝ) :
    Measurable (Function.uncurry (marcF g p₀ r)) := by
  have hn : Measurable (fun p : ℝ × X => ‖g p.2‖) := hg.norm.comp measurable_snd
  have hs : MeasurableSet {p : ℝ × X | p.1 < ‖g p.2‖} := measurableSet_lt measurable_fst hn
  refine Measurable.mul (Measurable.add ?_ ?_) ?_
  · exact (by fun_prop : Measurable fun p : ℝ × X => ENNReal.ofReal (2 / p.1)).mul
      (Measurable.ite hs hn.ennreal_ofReal measurable_const)
  · exact (by fun_prop : Measurable fun p : ℝ × X => ENNReal.ofReal ((2 / p.1) ^ p₀)).mul
      (Measurable.ite hs measurable_const (hn.pow_const p₀).ennreal_ofReal)
  · exact (measurable_fst.pow_const _).ennreal_ofReal

omit [SFinite μ] [MeasurableSpace Y] in
lemma marcF_int (g : X → ℂ) (hg : Measurable g) {p₀ : ℝ} (hp₀ : 0 < p₀) (r t : ℝ) :
    ∫⁻ x, marcF g p₀ r t x ∂μ =
      (ENNReal.ofReal (2 / t) * (∫⁻ x, ‖truncHi g t x‖ₑ ∂μ) +
        ENNReal.ofReal ((2 / t) ^ p₀) * (∫⁻ x, ‖truncLo g t x‖ₑ ^ p₀ ∂μ)) *
        ENNReal.ofReal (t ^ (r - 1)) := by
  simp only [enorm_truncHi, enorm_truncLo_rpow g t hp₀]
  have hs : MeasurableSet {x | t < ‖g x‖} := measurableSet_lt measurable_const hg.norm
  have m1 : Measurable (fun x => if t < ‖g x‖ then ENNReal.ofReal ‖g x‖ else 0) :=
    Measurable.ite hs hg.norm.ennreal_ofReal measurable_const
  have m2 : Measurable (fun x => if t < ‖g x‖ then 0 else ENNReal.ofReal (‖g x‖ ^ p₀)) :=
    Measurable.ite hs measurable_const (hg.norm.pow_const p₀).ennreal_ofReal
  unfold marcF
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [lintegral_add_left (m1.const_mul _), lintegral_const_mul _ m1,
    lintegral_const_mul _ m2]

omit [MeasurableSpace X] in
lemma marcF_point {p₀ r : ℝ} (hr1 : 1 < r) (hrp : r < p₀) (g : X → ℂ) (x : X) :
    ∫⁻ t in Ioi 0, marcF g p₀ r t x ≤
      ENNReal.ofReal (2 / (r - 1) + 2 ^ p₀ / (p₀ - r)) * ‖g x‖ₑ ^ r := by
  refine (lint_point hr1 hrp (norm_nonneg (g x))).trans (le_of_eq ?_)
  have : 0 < r - 1 := by linarith
  have : 0 < p₀ - r := by linarith
  rw [ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith)]

omit [SFinite ν] in
include P in
/-- The interpolation step with a common constant `A`. -/
lemma marc
    (hPhi : ∀ g t, P g → P (truncHi g t)) (hPlo : ∀ g t, P g → P (truncLo g t))
    (hlin : ∀ g g', P g → P g' → T (g + g') = T g + T g')
    (hmeasT : ∀ g, P g → Measurable (T g)) (hmeasg : ∀ g, P g → Measurable g)
    {p₀ : ℝ} (hp₀ : 1 < p₀)
    (h1 : ∀ g, P g → ∫⁻ y, ‖T g y‖ₑ ∂ν ≤ A * ∫⁻ x, ‖g x‖ₑ ∂μ)
    (h0 : ∀ g, P g → ∫⁻ y, ‖T g y‖ₑ ^ p₀ ∂ν ≤ A * ∫⁻ x, ‖g x‖ₑ ^ p₀ ∂μ)
    {r : ℝ} (hr1 : 1 < r) (hrp : r < p₀) (g : X → ℂ) (hg : P g) :
    ∫⁻ y, ‖T g y‖ₑ ^ r ∂ν ≤
      ENNReal.ofReal (r * (2 / (r - 1) + 2 ^ p₀ / (p₀ - r))) * A * ∫⁻ x, ‖g x‖ₑ ^ r ∂μ := by
  have hr0 : 0 < r := by linarith
  have hp0 : 0 < p₀ := by linarith
  have hlc := lintegral_rpow_eq_lintegral_meas_lt_mul ν (f := fun y => ‖T g y‖)
    (Filter.Eventually.of_forall (fun y => norm_nonneg _)) (hmeasT g hg).norm.aemeasurable hr0
  have e0 : ∫⁻ y, ‖T g y‖ₑ ^ r ∂ν = ∫⁻ y, ENNReal.ofReal (‖T g y‖ ^ r) ∂ν := by
    congr 1; ext y
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le]
  rw [e0, hlc]
  have hFm := marcF_meas g (hmeasg g hg) p₀ r
  have key : ∀ t ∈ Ioi (0 : ℝ), ν {y | t < ‖T g y‖} * ENNReal.ofReal (t ^ (r - 1)) ≤
      A * ∫⁻ x, marcF g p₀ r t x ∂μ := by
    intro t ht
    rw [marcF_int μ g (hmeasg g hg) hp0, ← mul_assoc]
    gcongr
    exact marc_step μ ν P T A hPhi hPlo hlin hmeasT hp0 h1 h0 g hg t ht
  calc ENNReal.ofReal r * ∫⁻ t in Ioi 0, ν {y | t < ‖T g y‖} * ENNReal.ofReal (t ^ (r - 1))
      ≤ ENNReal.ofReal r * ∫⁻ t in Ioi 0, A * ∫⁻ x, marcF g p₀ r t x ∂μ := by
        gcongr 1
        exact setLIntegral_mono' measurableSet_Ioi key
    _ = ENNReal.ofReal r * (A * ∫⁻ x, (∫⁻ t in Ioi 0, marcF g p₀ r t x) ∂μ) := by
        congr 1
        have hmi : Measurable (fun t => ∫⁻ x, marcF g p₀ r t x ∂μ) := hFm.lintegral_prod_right'
        rw [lintegral_const_mul _ hmi]
        congr 1
        exact lintegral_lintegral_swap hFm.aemeasurable
    _ ≤ ENNReal.ofReal r * (A * ∫⁻ x,
          ENNReal.ofReal (2 / (r - 1) + 2 ^ p₀ / (p₀ - r)) * ‖g x‖ₑ ^ r ∂μ) := by
        gcongr with x
        exact marcF_point hr1 hrp g x
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hr0.le]
        ring

end TaoBR.Tao49.PartI1
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartI1
/-- The scaling identity: with `λ = (A₁/A₀)^{1/(p₀-1)}`, `λ^{p₀} A₀ = A₁ λ`. -/
lemma lam_pow {p₀ A₁ A₀ : ℝ} (hp₀ : 1 < p₀) (hA₁ : 0 < A₁) (hA₀ : 0 < A₀) :
    ((A₁ / A₀) ^ (1 / (p₀ - 1))) ^ p₀ * A₀ = A₁ * (A₁ / A₀) ^ (1 / (p₀ - 1)) := by
  set l := (A₁ / A₀) ^ (1 / (p₀ - 1)) with hl
  have hl0 : 0 < l := Real.rpow_pos_of_pos (div_pos hA₁ hA₀) _
  have h1 : l ^ (p₀ - 1) = A₁ / A₀ := by
    rw [hl, ← Real.rpow_mul (div_pos hA₁ hA₀).le, one_div,
      inv_mul_cancel₀ (by linarith), Real.rpow_one]
  have h2 : l ^ p₀ = l ^ (p₀ - 1) * l := by
    rw [← Real.rpow_add_one hl0.ne']; ring_nf
  rw [h2, h1]; field_simp

/-- The constant: `A₁ λ / λ^r = A₁^{(p₀-r)/(p₀-1)} A₀^{(r-1)/(p₀-1)}`. -/
lemma lam_const {p₀ A₁ A₀ r : ℝ} (hp₀ : 1 < p₀) (hA₁ : 0 < A₁) (hA₀ : 0 < A₀) :
    (((A₁ / A₀) ^ (1 / (p₀ - 1))) ^ r)⁻¹ * (A₁ * (A₁ / A₀) ^ (1 / (p₀ - 1))) =
      A₁ ^ ((p₀ - r) / (p₀ - 1)) * A₀ ^ ((r - 1) / (p₀ - 1)) := by
  have hp : p₀ - 1 ≠ 0 := by linarith
  have hd : 0 < A₁ / A₀ := div_pos hA₁ hA₀
  have hl : 0 < (A₁ / A₀) ^ (1 / (p₀ - 1)) := Real.rpow_pos_of_pos hd _
  rw [Real.rpow_def_of_pos hl, Real.rpow_def_of_pos hd, Real.rpow_def_of_pos hA₁,
    Real.rpow_def_of_pos hA₀, Real.log_exp, Real.log_div hA₁.ne' hA₀.ne',
    ← Real.exp_neg, ← Real.exp_log hA₁]
  simp only [Real.log_exp, ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem interp_L1_Lp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (P : (X → ℂ) → Prop) (T : (X → ℂ) → Y → ℂ)
    (hPhi : ∀ g t, P g → P (fun x => if t < ‖g x‖ then g x else 0))
    (hPlo : ∀ g t, P g → P (fun x => if t < ‖g x‖ then 0 else g x))
    (hlin : ∀ g g', P g → P g' → T (g + g') = T g + T g')
    (hmeasT : ∀ g, P g → Measurable (T g)) (hmeasg : ∀ g, P g → Measurable g)
    {p₀ : ℝ} (hp₀ : 1 < p₀) {A₁ A₀ : ℝ} (hA₁ : 0 < A₁) (hA₀ : 0 < A₀)
    (h1 : ∀ g, P g → ∫⁻ y, ‖T g y‖ₑ ∂ν ≤ ENNReal.ofReal A₁ * ∫⁻ x, ‖g x‖ₑ ∂μ)
    (h0 : ∀ g, P g → ∫⁻ y, ‖T g y‖ₑ ^ p₀ ∂ν ≤ ENNReal.ofReal A₀ * ∫⁻ x, ‖g x‖ₑ ^ p₀ ∂μ)
    {r : ℝ} (hr1 : 1 < r) (hrp : r < p₀) (g : X → ℂ) (hg : P g) :
    ∫⁻ y, ‖T g y‖ₑ ^ r ∂ν ≤
      ENNReal.ofReal (2 * r * (2 / (r - 1) + 2 ^ p₀ / (p₀ - r)) *
        A₁ ^ ((p₀ - r) / (p₀ - 1)) * A₀ ^ ((r - 1) / (p₀ - 1))) * ∫⁻ x, ‖g x‖ₑ ^ r ∂μ := by
  set l := (A₁ / A₀) ^ (1 / (p₀ - 1)) with hl
  have hl0 : 0 < l := Real.rpow_pos_of_pos (div_pos hA₁ hA₀) _
  have hp0 : 0 < p₀ := by linarith
  have hr0 : 0 < r := by linarith
  set T' : (X → ℂ) → Y → ℂ := fun g y => (l : ℂ) * T g y with hT'
  have hn : ∀ g y, ‖T' g y‖ₑ = ENNReal.ofReal l * ‖T g y‖ₑ := by
    intro g y
    rw [hT', enorm_mul, ← ofReal_norm (l : ℂ), Complex.norm_real, Real.norm_of_nonneg hl0.le]
  have h1' : ∀ g, P g → ∫⁻ y, ‖T' g y‖ₑ ∂ν ≤ ENNReal.ofReal (A₁ * l) * ∫⁻ x, ‖g x‖ₑ ∂μ := by
    intro g hg
    simp_rw [hn]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hA₁.le, mul_comm _
      (ENNReal.ofReal l), mul_assoc]
    gcongr
    exact h1 g hg
  have h0' : ∀ g, P g → ∫⁻ y, ‖T' g y‖ₑ ^ p₀ ∂ν ≤
      ENNReal.ofReal (A₁ * l) * ∫⁻ x, ‖g x‖ₑ ^ p₀ ∂μ := by
    intro g hg
    simp_rw [hn, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top),
      ← lam_pow hp₀ hA₁ hA₀, ENNReal.ofReal_mul (Real.rpow_nonneg hl0.le _),
      ENNReal.ofReal_rpow_of_nonneg hl0.le hp0.le, mul_assoc]
    gcongr
    exact h0 g hg
  have hlin' : ∀ g g', P g → P g' → T' (g + g') = T' g + T' g' := by
    intro g g' hg hg'
    funext y
    simp only [hT', hlin g g' hg hg', Pi.add_apply, mul_add]
  have hmeasT' : ∀ g, P g → Measurable (T' g) := fun g hg => (hmeasT g hg).const_mul _
  have hm := marc μ ν P T' (ENNReal.ofReal (A₁ * l)) (fun g t hg => hPhi g t hg)
    (fun g t hg => hPlo g t hg) hlin' hmeasT' hmeasg hp₀ h1' h0' hr1 hrp g hg
  simp_rw [hn, ENNReal.mul_rpow_of_nonneg _ _ hr0.le] at hm
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top),
    ENNReal.ofReal_rpow_of_nonneg hl0.le hr0.le] at hm
  have hlr : 0 < l ^ r := Real.rpow_pos_of_pos hl0 _
  have hne : ENNReal.ofReal (l ^ r) ≠ 0 := by simpa using hlr
  have key : ∫⁻ y, ‖T g y‖ₑ ^ r ∂ν ≤ ENNReal.ofReal ((l ^ r)⁻¹) *
      (ENNReal.ofReal (r * (2 / (r - 1) + 2 ^ p₀ / (p₀ - r))) * ENNReal.ofReal (A₁ * l) *
        ∫⁻ x, ‖g x‖ₑ ^ r ∂μ) := by
    rw [ENNReal.ofReal_inv_of_pos hlr, ← ENNReal.div_eq_inv_mul,
      ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hm
  have hc : 0 ≤ r * (2 / (r - 1) + 2 ^ p₀ / (p₀ - r)) := by
    have : 0 < r - 1 := by linarith
    have : 0 < p₀ - r := by linarith
    positivity
  calc _ ≤ _ := key
    _ = ENNReal.ofReal ((l ^ r)⁻¹ * (r * (2 / (r - 1) + 2 ^ p₀ / (p₀ - r))) * (A₁ * l)) *
          ∫⁻ x, ‖g x‖ₑ ^ r ∂μ := by
        rw [ENNReal.ofReal_mul (show 0 ≤ (l ^ r)⁻¹ * (r * (2 / (r - 1) + 2 ^ p₀ / (p₀ - r))) by
          positivity), ENNReal.ofReal_mul (show 0 ≤ (l ^ r)⁻¹ by positivity)]
        ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (zero_le)
        have e : (l ^ r)⁻¹ * (r * (2 / (r - 1) + 2 ^ p₀ / (p₀ - r))) * (A₁ * l) =
            r * (2 / (r - 1) + 2 ^ p₀ / (p₀ - r)) *
              (A₁ ^ ((p₀ - r) / (p₀ - 1)) * A₀ ^ ((r - 1) / (p₀ - 1))) := by
          rw [← lam_const hp₀ hA₁ hA₀]; ring
        rw [e]
        have : 0 ≤ A₁ ^ ((p₀ - r) / (p₀ - 1)) * A₀ ^ ((r - 1) / (p₀ - 1)) := by positivity
        nlinarith

end TaoBR.Tao49.PartI1
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
/-! ## Interpolation -/
alias interp_L1_Lp := TaoBR.Tao49.PartI1.interp_L1_Lp

/-! ## The linearized measure -/
/-- `Φ(x) = ∇_y φ(x, y₀)`. -/
noncomputable def Grad {n m : ℕ} (φ : E n → E m → ℝ) (y₀ : E m) (x : E n) : E m :=
  gradient (fun y => φ x y) y₀

/-- `μ_q = Φ_* (|ψ(·, y₀)|^q dx)`. -/
noncomputable def muQ {n m : ℕ} (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ) (y₀ : E m) (q : ℝ) :
    Measure (E m) :=
  (volume.withDensity fun x => ‖ψ x y₀‖ₑ ^ q).map (Grad φ y₀)

/-- The push-forward of `μ` under `ξ ↦ ξ / λ`. -/
noncomputable def scaleM {m : ℕ} (lam : ℝ) (μ : Measure (E m)) : Measure (E m) :=
  μ.map fun ξ => lam⁻¹ • ξ

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartL
/-!
# Part L of the Theorem 4.9 Blueprint: `local_estimate_of_oscillatoryOp_le`

The linearization of the oscillatory operator `S_R` at `y₀`: test the `Lᵖ` bound for `S_R` on
`f(y) = g(R (y - y₀))` with `R = L^{m+2}`; after the change of variables `y = y₀ + R⁻¹ z`,
`R^m 𝐞(R φ(x, y₀)) S_R f(x)` differs from `ψ(x, y₀) ĝ(∇_y φ(x, y₀))` by at most
`C (L²/R) ‖g‖₁ 1_K(x)` (Taylor for the phase, Lipschitz for `ψ`), and
`‖g‖₁ ≤ |B(0, L)|^{1 - 1/p} ‖g‖_p`.

No Blueprint definitions are needed beyond `Definitions.Def_TaoBR`.
-/
/-! ## Operator norms -/
/-- A finite bound on `opNorm` gives the inequality for each `f ∈ Lᵖ`. -/
theorem eLpNorm_le_of_opNorm_le {n m : ℕ} {p q : ℝ≥0∞} {T : (E m → ℂ) → (E n → ℂ)}
    {B : ℝ≥0∞} (hB : opNorm p q T ≤ B) (hBt : B ≠ ⊤) {f : E m → ℂ} (hf : MemLp f p volume) :
    eLpNorm (T f) q volume ≤ B * eLpNorm f p volume := by
  set S := {C : ℝ≥0∞ | ∀ f : E m → ℂ, MemLp f p volume →
    eLpNorm (T f) q volume ≤ C * eLpNorm f p volume} with hSdef
  have hS' : sInf S ≤ B := hB
  have hmem : ∀ C ∈ S, eLpNorm (T f) q volume ≤ C * eLpNorm f p volume := fun C hC => hC f hf
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hS' (zero_le))
  by_cases h0 : eLpNorm f p volume = 0
  · have hne : S.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [h, sInf_empty] at hS'
      exact hBt (top_le_iff.mp hS')
    obtain ⟨C, hC⟩ := hne
    simpa [h0] using hmem C hC
  · have htop : eLpNorm f p volume ≠ ⊤ := hf.eLpNorm_ne_top
    rw [← ENNReal.div_le_iff h0 htop]
    exact le_sInf fun C hC => (ENNReal.div_le_iff h0 htop).mpr (hmem C hC)

/-! ## Bounded functions with bounded support -/
theorem memLp_of_bdd {m : ℕ} {h : E m → ℂ} (hm : Measurable h) {B : ℝ} (hB : ∀ y, ‖h y‖ ≤ B)
    {c : E m} {r : ℝ} (hs : ∀ y, y ∉ closedBall c r → h y = 0) (p : ℝ≥0∞) :
    MemLp h p volume :=
  (memLp_top_of_bound hm.aestronglyMeasurable B (Filter.Eventually.of_forall hB)).mono_exponent_of_measure_support_ne_top
    hs measure_closedBall_lt_top.ne le_top

/-! ## Scaling -/
theorem eLpNorm_comp_smul_sub {m : ℕ} {g : E m → ℂ} (hg : Measurable g) {R : ℝ} (hR : R ≠ 0)
    (y₀ : E m) (p : ℝ≥0∞) :
    eLpNorm (fun y => g (R • (y - y₀))) p volume =
      ENNReal.ofReal |(R ^ m)⁻¹| ^ (1 / p).toReal * eLpNorm g p volume := by
  have h1 : eLpNorm (fun y => g (R • (y - y₀))) p volume =
      eLpNorm (fun y => g (R • y)) p volume :=
    eLpNorm_comp_measurePreserving (p := p) (g := fun y => g (R • y))
      (hg.comp (measurable_const_smul R)).aestronglyMeasurable
      (measurePreserving_sub_right volume y₀)
  rw [h1]
  have h2 : eLpNorm (fun y => g (R • y)) p volume =
      eLpNorm g p (Measure.map (fun y : E m => R • y) volume) :=
    (eLpNorm_map_measure hg.aestronglyMeasurable
      (measurable_const_smul R).aemeasurable).symm
  rw [h2, Measure.map_addHaar_smul volume hR, finrank_euclideanSpace_fin,
    eLpNorm_smul_measure_of_ne_zero, smul_eq_mul]
  simp [hR]

theorem integral_comp_smul_sub {m : ℕ} (k g : E m → ℂ) {R : ℝ} (hR : R ≠ 0) (y₀ : E m) :
    ∫ y, k y * g (R • (y - y₀)) = |(R ^ m)⁻¹| • ∫ z, k (y₀ + R⁻¹ • z) * g z := by
  have h1 : ∫ y, k y * g (R • (y - y₀)) = ∫ w, k (w + y₀) * g (R • w) := by
    rw [← integral_add_right_eq_self (μ := volume) _ y₀]
    simp
  rw [h1]
  have h2 := Measure.integral_comp_smul (volume : Measure (E m))
    (fun z => k (y₀ + R⁻¹ • z) * g z) R
  rw [finrank_euclideanSpace_fin] at h2
  rw [← h2]
  congr 1
  ext w
  simp [inv_smul_smul₀ hR, add_comm]

/-! ## Taylor bound for the phase -/
theorem taylor_bound {n m : ℕ} (φ : E n → E m → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ)) {K : Set (E n)} (hK : IsCompact K)
    (y₀ : E m) :
    ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ x ∈ K, ∀ h : E m, ‖h‖ ≤ 1 →
      |φ x (y₀ + h) - φ x y₀ - ⟪h, gradient (fun y => φ x y) y₀⟫| ≤ C2 * ‖h‖ ^ 2 := by
  set G : E n × E m → (E m →L[ℝ] ℝ) := fun q =>
    (fderiv ℝ (Function.uncurry φ) q).comp (ContinuousLinearMap.inr ℝ (E n) (E m)) with hG
  have hGd : ContDiff ℝ 1 G := by
    have : ContDiff ℝ 1 (fderiv ℝ (Function.uncurry φ)) :=
      hφ.fderiv_right (by norm_cast)
    exact this.clm_comp contDiff_const
  have hpart : ∀ x y, HasFDerivAt (fun y' => φ x y') (G (x, y)) y := by
    intro x y
    have h1 : HasFDerivAt (Function.uncurry φ) (fderiv ℝ (Function.uncurry φ) (x, y)) (x, y) :=
      ((hφ.differentiable (by simp)) (x, y)).hasFDerivAt
    exact h1.comp y (hasFDerivAt_prodMk_right x y)
  have hGy : ∀ x y, HasFDerivAt (fun y' => G (x, y'))
      ((fderiv ℝ G (x, y)).comp (ContinuousLinearMap.inr ℝ (E n) (E m))) y := by
    intro x y
    have h1 : HasFDerivAt G (fderiv ℝ G (x, y)) (x, y) :=
      ((hGd.differentiable one_ne_zero) (x, y)).hasFDerivAt
    exact h1.comp y (hasFDerivAt_prodMk_right x y)
  have hcont : Continuous (fun q => fderiv ℝ G q) := hGd.continuous_fderiv one_ne_zero
  obtain ⟨C2', hC2'⟩ :=
    (hK.prod (isCompact_closedBall y₀ 1)).exists_bound_of_continuousOn
      (f := fun q => fderiv ℝ G q) hcont.continuousOn
  refine ⟨max C2' 0, le_max_right _ _, ?_⟩
  set C2 := max C2' 0
  intro x hx h hh
  have step1 : ∀ h' : E m, ‖h'‖ ≤ 1 → ‖G (x, y₀ + h') - G (x, y₀)‖ ≤ C2 * ‖h'‖ := by
    intro h' hh'
    have := (convex_closedBall y₀ 1).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun y' => G (x, y')) (fun y _ => (hGy x y).hasFDerivWithinAt) (C := C2) ?_
      (mem_closedBall_self zero_le_one) (y := y₀ + h') ?_
    · simpa using this
    · intro y hy
      calc ‖(fderiv ℝ G (x, y)).comp (ContinuousLinearMap.inr ℝ (E n) (E m))‖
          ≤ ‖fderiv ℝ G (x, y)‖ * ‖ContinuousLinearMap.inr ℝ (E n) (E m)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ C2 * 1 := mul_le_mul (le_trans (hC2' (x, y) ⟨hx, hy⟩) (le_max_left _ _))
            (ContinuousLinearMap.norm_inr_le_one ..) (norm_nonneg _) (le_max_right _ _)
        _ = C2 := mul_one _
    · simpa [dist_eq_norm] using hh'
  set u : E m → ℝ := fun h' => φ x (y₀ + h') - G (x, y₀) h' with hu_def
  have hu : ∀ h', HasFDerivAt u (G (x, y₀ + h') - G (x, y₀)) h' := by
    intro h'
    have h1 : HasFDerivAt (fun h' => φ x (y₀ + h')) (G (x, y₀ + h')) h' := by
      have := (hpart x (y₀ + h')).comp h' ((hasFDerivAt_id h').const_add y₀)
      rw [ContinuousLinearMap.comp_id] at this
      exact this
    exact h1.sub (G (x, y₀)).hasFDerivAt
  have hmv := (convex_closedBall (0 : E m) ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := u) (fun y _ => (hu y).hasFDerivWithinAt) (C := C2 * ‖h‖) ?_
      (mem_closedBall_self (norm_nonneg h)) (y := h) (by simp)
  · have hgrad : ⟪h, gradient (fun y => φ x y) y₀⟫ = G (x, y₀) h := by
      rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply, (hpart x y₀).fderiv]
    rw [hgrad]
    have e1 : u h - u 0 = φ x (y₀ + h) - φ x y₀ - G (x, y₀) h := by
      simp [hu_def]; ring
    rw [e1, Real.norm_eq_abs] at hmv
    calc _ ≤ C2 * ‖h‖ * ‖h - 0‖ := hmv
      _ = C2 * ‖h‖ ^ 2 := by rw [sub_zero]; ring
  · intro y hy
    have hy' : ‖y‖ ≤ ‖h‖ := by simpa using hy
    calc ‖G (x, y₀ + y) - G (x, y₀)‖ ≤ C2 * ‖y‖ := step1 y (hy'.trans hh)
      _ ≤ C2 * ‖h‖ := mul_le_mul_of_nonneg_left hy' (le_max_right _ _)

/-! ## The kernel comparison -/
theorem norm_cexp_sub_le (a b : ℝ) :
    ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖ ≤ |a - b| := by
  have e : (b : ℂ) * Complex.I + Complex.I * ((a - b : ℝ) : ℂ) = a * Complex.I := by
    push_cast; ring
  have : Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I) =
      Complex.exp (b * Complex.I) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add, e]
  rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)

theorem norm_exp_mul_sub_le {θA θB τ M ℓ : ℝ} {ψ0 ψ1 : ℂ} (hψ0 : ‖ψ0‖ ≤ M)
    (hψ : ‖ψ0 - ψ1‖ ≤ ℓ) (hθ : |θA - θB| ≤ τ) (hτ : 0 ≤ τ) :
    ‖Complex.exp (θA * Complex.I) * ψ0 - Complex.exp (θB * Complex.I) * ψ1‖ ≤ τ * M + ℓ := by
  have e : Complex.exp (θA * Complex.I) * ψ0 - Complex.exp (θB * Complex.I) * ψ1 =
      (Complex.exp (θA * Complex.I) - Complex.exp (θB * Complex.I)) * ψ0 +
        Complex.exp (θB * Complex.I) * (ψ0 - ψ1) := by ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul ((norm_cexp_sub_le _ _).trans hθ) hψ0 (norm_nonneg _) hτ
  · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hψ

theorem kernel_bound {n m : ℕ} (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ) {K : Set (E n)}
    {C2 M Lψ : ℝ} (hC2 : 0 ≤ C2) (hM : ∀ x y, ‖ψ x y‖ ≤ M)
    (hLip : ∀ x y y', ‖ψ x y - ψ x y'‖ ≤ Lψ * ‖y - y'‖) (hLψ : 0 ≤ Lψ) (y₀ : E m)
    (htay : ∀ x ∈ K, ∀ h : E m, ‖h‖ ≤ 1 →
      |φ x (y₀ + h) - φ x y₀ - ⟪h, gradient (fun y => φ x y) y₀⟫| ≤ C2 * ‖h‖ ^ 2)
    {L R : ℝ} (hL : 1 ≤ L) (hLR : L ≤ R) {x : E n} (hx : x ∈ K) {z : E m} (hz : ‖z‖ ≤ L) :
    ‖ψ x y₀ * (𝐞 (-⟪z, gradient (fun y => φ x y) y₀⟫) : ℂ) -
        Complex.exp (((2 * Real.pi * (R * φ x y₀) : ℝ) : ℂ) * Complex.I) *
          (Complex.exp (-(2 * Real.pi * Complex.I * ((R * φ x (y₀ + R⁻¹ • z) : ℝ) : ℂ))) *
            ψ x (y₀ + R⁻¹ • z))‖ ≤
      (2 * Real.pi * C2 * M + Lψ) * L ^ 2 / R := by
  set Φ := gradient (fun y => φ x y) y₀
  set h := R⁻¹ • z with h_def
  have hR : 0 < R := by linarith
  have hh : ‖h‖ = ‖z‖ / R := by
    rw [h_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, div_eq_inv_mul]
  have hh1 : ‖h‖ ≤ 1 := by rw [hh, div_le_one hR]; linarith
  have hzR : ⟪z, Φ⟫ = R * ⟪h, Φ⟫ := by
    rw [h_def, real_inner_smul_left]; field_simp
  set θA : ℝ := 2 * Real.pi * (-⟪z, Φ⟫) with hθA
  set θB : ℝ := 2 * Real.pi * (R * φ x y₀) + -(2 * Real.pi * (R * φ x (y₀ + h))) with hθB
  have e1 : ψ x y₀ * (𝐞 (-⟪z, Φ⟫) : ℂ) = Complex.exp (θA * Complex.I) * ψ x y₀ := by
    rw [Real.fourierChar_apply, mul_comm]
  have e2 : Complex.exp (((2 * Real.pi * (R * φ x y₀) : ℝ) : ℂ) * Complex.I) *
      (Complex.exp (-(2 * Real.pi * Complex.I * ((R * φ x (y₀ + h) : ℝ) : ℂ))) * ψ x (y₀ + h)) =
        Complex.exp (θB * Complex.I) * ψ x (y₀ + h) := by
    rw [← mul_assoc, ← Complex.exp_add, hθB]
    congr 2
    push_cast; ring
  rw [e1, e2]
  have hθ : |θA - θB| ≤ 2 * Real.pi * C2 * L ^ 2 / R := by
    have : θA - θB = 2 * Real.pi * R * (φ x (y₀ + h) - φ x y₀ - ⟪h, Φ⟫) := by
      rw [hθA, hθB, hzR]; ring
    rw [this, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi * R)]
    calc 2 * Real.pi * R * |φ x (y₀ + h) - φ x y₀ - ⟪h, Φ⟫|
        ≤ 2 * Real.pi * R * (C2 * ‖h‖ ^ 2) := by
          gcongr; exact htay x hx h hh1
      _ = 2 * Real.pi * C2 * ‖z‖ ^ 2 / R := by rw [hh]; field_simp
      _ ≤ 2 * Real.pi * C2 * L ^ 2 / R := by gcongr
  have hψd : ‖ψ x y₀ - ψ x (y₀ + h)‖ ≤ Lψ * L ^ 2 / R := by
    calc _ ≤ Lψ * ‖y₀ - (y₀ + h)‖ := hLip _ _ _
      _ = Lψ * (‖z‖ / R) := by rw [sub_add_cancel_left, norm_neg, hh]
      _ ≤ Lψ * (L ^ 2 / R) := by
          gcongr
          nlinarith
      _ = _ := by ring
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x y₀)
  calc _ ≤ 2 * Real.pi * C2 * L ^ 2 / R * M + Lψ * L ^ 2 / R :=
        norm_exp_mul_sub_le (hM x y₀) hψd hθ (by positivity)
    _ = _ := by ring

theorem norm_cexp_neg_two_pi_I (r : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * (r : ℂ)))‖ = 1 := by
  have : -(2 * Real.pi * Complex.I * (r : ℂ)) = ((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-! ## The pointwise comparison -/
theorem pointwise_bound {n m : ℕ} (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ)
    (hφc : Continuous (Function.uncurry φ)) (hψc : Continuous (Function.uncurry ψ))
    {K : Set (E n)} (hKψ : ∀ x, x ∉ K → ∀ y, ψ x y = 0)
    {C2 M Lψ : ℝ} (hC2 : 0 ≤ C2) (hM : ∀ x y, ‖ψ x y‖ ≤ M)
    (hLip : ∀ x y y', ‖ψ x y - ψ x y'‖ ≤ Lψ * ‖y - y'‖) (hLψ : 0 ≤ Lψ) (y₀ : E m)
    (htay : ∀ x ∈ K, ∀ h : E m, ‖h‖ ≤ 1 →
      |φ x (y₀ + h) - φ x y₀ - ⟪h, gradient (fun y => φ x y) y₀⟫| ≤ C2 * ‖h‖ ^ 2)
    {L R : ℝ} (hL : 1 ≤ L) (hLR : L ≤ R) {g : E m → ℂ}
    (hgi : Integrable g) (hgs : ∀ y, y ∉ closedBall (0 : E m) L → g y = 0) (x : E n) :
    ‖linearizedRestriction φ ψ y₀ g x‖ ≤
      (R ^ m : ℝ) * ‖oscillatoryOp φ ψ R (fun y => g (R • (y - y₀))) x‖ +
        K.indicator (fun _ => (2 * Real.pi * C2 * M + Lψ) * L ^ 2 / R * ∫ z, ‖g z‖) x := by
  have hR : 0 < R := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x y₀)
  by_cases hx : x ∉ K
  · simp only [linearizedRestriction, hKψ x hx, zero_mul, norm_zero, Set.indicator_of_notMem hx,
      add_zero]
    positivity
  rw [not_not] at hx
  rw [Set.indicator_of_mem hx]
  set Φ := gradient (fun y => φ x y) y₀ with hΦ
  set e0 : ℂ := Complex.exp (((2 * Real.pi * (R * φ x y₀) : ℝ) : ℂ) * Complex.I) with he0
  set k : E m → ℂ := fun y =>
    Complex.exp (-(2 * Real.pi * Complex.I * ((R * φ x y : ℝ) : ℂ))) * ψ x y with hk
  set A : E m → ℂ := fun z => ψ x y₀ * (𝐞 (-⟪z, Φ⟫) : ℂ) with hA
  set B : E m → ℂ := fun z => e0 * k (y₀ + R⁻¹ • z) with hB
  set S := oscillatoryOp φ ψ R (fun y => g (R • (y - y₀))) x with hS
  have hLRx : linearizedRestriction φ ψ y₀ g x = ∫ z, A z * g z := by
    simp only [linearizedRestriction, Real.fourier_eq, Circle.smul_def, smul_eq_mul, hA]
    rw [← integral_const_mul]
    congr 1; ext z; ring
  have hSx : ((R ^ m : ℝ) : ℂ) * e0 * S = ∫ z, B z * g z := by
    have h1 : S = ∫ y, k y * g (R • (y - y₀)) := rfl
    rw [h1, integral_comp_smul_sub k g hR.ne' y₀, Complex.real_smul,
      abs_of_pos (inv_pos.mpr (pow_pos hR m))]
    have h2 : ((R ^ m : ℝ) : ℂ) * (((R ^ m)⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (pow_pos hR m).ne', Complex.ofReal_one]
    calc ((R ^ m : ℝ) : ℂ) * e0 * ((((R ^ m)⁻¹ : ℝ) : ℂ) * ∫ z, k (y₀ + R⁻¹ • z) * g z)
        = (((R ^ m : ℝ) : ℂ) * (((R ^ m)⁻¹ : ℝ) : ℂ)) * (e0 * ∫ z, k (y₀ + R⁻¹ • z) * g z) := by
          ring
      _ = ∫ z, B z * g z := by
          rw [h2, one_mul, ← integral_const_mul]
          congr 1; ext z; simp only [hB]; ring
  have hAc : Continuous A := by
    simp only [hA]
    fun_prop
  have hBc : Continuous B := by
    simp only [hB, hk]
    have h1 : Continuous fun z : E m => φ x (y₀ + R⁻¹ • z) :=
      hφc.comp (by fun_prop : Continuous fun z : E m => (x, y₀ + R⁻¹ • z))
    have h2 : Continuous fun z : E m => ψ x (y₀ + R⁻¹ • z) :=
      hψc.comp (by fun_prop : Continuous fun z : E m => (x, y₀ + R⁻¹ • z))
    fun_prop
  have hAb : ∀ z, ‖A z‖ ≤ M := by
    intro z
    simp only [hA, norm_mul, Circle.norm_coe, mul_one]
    exact hM x y₀
  have hBb : ∀ z, ‖B z‖ ≤ M := by
    intro z
    simp only [hB, hk, he0, norm_mul, Complex.norm_exp_ofReal_mul_I, norm_cexp_neg_two_pi_I,
      one_mul]
    exact hM _ _
  have hAi : Integrable (fun z => A z * g z) :=
    hgi.bdd_mul hAc.aestronglyMeasurable (Filter.Eventually.of_forall hAb)
  have hBi : Integrable (fun z => B z * g z) :=
    hgi.bdd_mul hBc.aestronglyMeasurable (Filter.Eventually.of_forall hBb)
  set c := (2 * Real.pi * C2 * M + Lψ) * L ^ 2 / R with hc
  have hD : ‖∫ z, (A z * g z - B z * g z)‖ ≤ c * ∫ z, ‖g z‖ := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hgi.norm.const_mul c) (Filter.Eventually.of_forall ?_)
    intro z
    rw [← sub_mul, norm_mul]
    by_cases hz : g z = 0
    · simp [hz]
    · have hz' : ‖z‖ ≤ L := by
        by_contra hcon
        exact hz (hgs z (by simpa using hcon))
      gcongr
      exact kernel_bound φ ψ hC2 hM hLip hLψ y₀ htay hL hLR hx hz'
  have hsplit : linearizedRestriction φ ψ y₀ g x =
      ((R ^ m : ℝ) : ℂ) * e0 * S + ∫ z, (A z * g z - B z * g z) := by
    rw [integral_sub hAi hBi, hLRx, hSx]; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ hD)
  rw [norm_mul, norm_mul, he0, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (pow_pos hR m)]

theorem oscillatoryOp_stronglyMeasurable {n m : ℕ} (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ)
    (hφc : Continuous (Function.uncurry φ)) (hψc : Continuous (Function.uncurry ψ)) (R : ℝ)
    {f : E m → ℂ} (hf : Measurable f) : StronglyMeasurable (oscillatoryOp φ ψ R f) := by
  unfold oscillatoryOp kernelOp
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  have h1 : Continuous fun q : E n × E m => φ q.1 q.2 := hφc
  have h2 : Continuous fun q : E n × E m => ψ q.1 q.2 := hψc
  have h3 : Continuous fun q : E n × E m =>
      Complex.exp (-(2 * Real.pi * Complex.I * ((R * φ q.1 q.2 : ℝ) : ℂ))) * ψ q.1 q.2 := by
    fun_prop
  exact h3.measurable.mul (hf.comp measurable_snd)

/-! ## Hölder and indicator bounds -/
theorem rpow_le_of_le_one_le {x X : ℝ≥0∞} {e : ℝ} (hxX : x ≤ X) (hX : 1 ≤ X) (he0 : 0 ≤ e)
    (he1 : e ≤ 1) : x ^ e ≤ X :=
  calc x ^ e ≤ X ^ e := ENNReal.rpow_le_rpow hxX he0
    _ ≤ X ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hX he1
    _ = X := ENNReal.rpow_one X

theorem one_div_toReal_mem {p : ℝ≥0∞} (hp : 1 ≤ p) : 0 ≤ 1 / p.toReal ∧ 1 / p.toReal ≤ 1 := by
  refine ⟨by positivity, ?_⟩
  by_cases ht : p = ⊤
  · simp [ht]
  · have : 1 ≤ p.toReal := by
      have := ENNReal.toReal_mono ht hp
      simpa using this
    exact (div_le_one (by linarith)).mpr this

theorem le_ofReal_toReal_add_one {x : ℝ≥0∞} (hx : x ≠ ⊤) : x ≤ ENNReal.ofReal (x.toReal + 1) :=
  calc x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hx).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

theorem eLpNorm_one_le {m : ℕ} {g : E m → ℂ} (hgm : AEStronglyMeasurable g volume) {L : ℝ}
    (hL : 1 ≤ L) (hgs : ∀ y, y ∉ closedBall (0 : E m) L → g y = 0) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm g 1 volume ≤ eLpNorm g p volume *
      ENNReal.ofReal (L ^ m * ((volume (ball (0 : E m) 1)).toReal + 1)) := by
  have hsupp : Function.support g ⊆ closedBall 0 L := by
    intro y hy
    by_contra h
    exact hy (hgs y h)
  rw [← eLpNorm_restrict_eq_of_support_subset (μ := volume) (p := 1) hsupp]
  have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := volume.restrict (closedBall (0 : E m) L)) hp hgm.restrict
  rw [Measure.restrict_apply_univ] at h2
  refine h2.trans (mul_le_mul' (eLpNorm_mono_measure _ Measure.restrict_le_self) ?_)
  obtain ⟨h0, h1⟩ := one_div_toReal_mem hp
  have hone : 1 / (1 : ℝ≥0∞).toReal = 1 := by simp
  rw [hone]
  have hβ : 0 ≤ (volume (ball (0 : E m) 1)).toReal := ENNReal.toReal_nonneg
  apply rpow_le_of_le_one_le
  · rw [Measure.addHaar_closedBall _ _ (by linarith : (0 : ℝ) ≤ L), finrank_euclideanSpace_fin,
      ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact le_ofReal_toReal_add_one measure_ball_lt_top.ne
  · rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have : 1 ≤ L ^ m := one_le_pow₀ hL
    nlinarith
  · linarith
  · linarith

theorem eLpNorm_indicator_le {n : ℕ} {K : Set (E n)} (hK : IsCompact K) {κ : ℝ} (hκ : 0 ≤ κ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (K.indicator fun _ => κ) p volume ≤
      ENNReal.ofReal κ * ENNReal.ofReal ((volume K).toReal + 1) := by
  refine (eLpNorm_indicator_const_le κ p).trans ?_
  rw [Real.enorm_of_nonneg hκ]
  obtain ⟨h0, h1⟩ := one_div_toReal_mem hp
  gcongr
  apply rpow_le_of_le_one_le (le_ofReal_toReal_add_one hK.measure_lt_top.ne) _ h0 h1
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := volume K)])

/-! ## Exponent bookkeeping -/
theorem conjExp_inv_toReal {p : ℝ≥0∞} (hp : 1 ≤ p) :
    (conjExp p)⁻¹.toReal = 1 - (1 / p).toReal := by
  unfold conjExp
  rw [inv_inv, ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr hp) ENNReal.one_ne_top,
    ENNReal.toReal_one, one_div]

theorem scale_real {m : ℕ} {R D ε' t : ℝ} (hR : 0 < R) :
    R ^ m * (D * R ^ (-((m : ℝ) * (1 - t)) + ε')) * |(R ^ m)⁻¹| ^ t = D * R ^ ε' := by
  rw [abs_of_pos (inv_pos.mpr (pow_pos hR m)), ← Real.rpow_natCast, ← Real.rpow_neg hR.le,
    ← Real.rpow_mul hR.le]
  have : R ^ (m : ℝ) * R ^ (-((m : ℝ) * (1 - t)) + ε') * R ^ (-(m : ℝ) * t) = R ^ ε' := by
    rw [← Real.rpow_add hR, ← Real.rpow_add hR]
    congr 1
    ring
  calc R ^ (m : ℝ) * (D * R ^ (-((m : ℝ) * (1 - t)) + ε')) * R ^ (-(m : ℝ) * t)
      = D * (R ^ (m : ℝ) * R ^ (-((m : ℝ) * (1 - t)) + ε') * R ^ (-(m : ℝ) * t)) := by ring
    _ = D * R ^ ε' := by rw [this]

theorem pow_rpow_div {m : ℕ} {L ε : ℝ} (hL : 0 ≤ L) :
    (L ^ (m + 2)) ^ (ε / (m + 2)) = L ^ ε := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
  congr 1
  push_cast
  field_simp

/-! ## The Blueprint lemma -/
/-- **L1 (linearization).** `hS` gives the localized estimate for `ℜ_{y₀}` with loss `L^ε`, for
bounded measurable `g` supported in `B(0, L)`.

Proof: fix `ε`, let `R = L^{m+2}` and `f(y) = g(R (y - y₀))` (bounded, compact support, so
`MemLp f p`). From `opNorm p p (S_R) ≤ C_{ε'} R^{-m/p' + ε'}` (`ε' = ε/(m+2)`; an `opNorm` bound
gives the inequality for each `MemLp f`): `‖S_R f‖_p ≤ C R^{-m/p'+ε'} R^{-m/p} ‖g‖_p`. Change of
variables `y = y₀ + R⁻¹ z`: `R^m 𝐞(R φ(x, y₀)) S_R f(x) = ∫ 𝐞(-⟪Φ(x), z⟫) 𝐞(-E(x, z))
ψ(x, y₀ + z/R) g(z) dz` with `E(x,z) = R φ(x, y₀ + z/R) - R φ(x, y₀) - ⟪Φ(x), z⟫`, `|E| ≤ C |z|²/R`
(Taylor, second `y`-derivatives bounded on a compact set). So `ψ(x, y₀) ĝ(Φ(x))` differs from it
by at most `C (L/R + L²/R) ‖g‖₁ 1_K(x)` with `K` compact (`ψ(x, ·) = 0` near `y₀` off `K`), and
`‖g‖₁ ≤ |B(0, L)|^{1 - 1/p} ‖g‖_p`. For `p = ∞` the same estimates hold with `1/p = 0`. -/
theorem local_estimate_of_oscillatoryOp_le {n m : ℕ} (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hS : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      opNorm p p (oscillatoryOp φ ψ R) ≤
        ENNReal.ofReal (C * R ^ (-((m : ℝ) * (conjExp p)⁻¹.toReal) + ε)))
    (y₀ : E m) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ L : ℝ, 1 ≤ L → ∀ g : E m → ℂ, Measurable g →
      (∃ B : ℝ, ∀ y, ‖g y‖ ≤ B) → (∀ y, y ∉ closedBall (0 : E m) L → g y = 0) →
        eLpNorm (linearizedRestriction φ ψ y₀ g) p volume ≤
          ENNReal.ofReal (C * L ^ ε) * eLpNorm g p volume := by
  intro ε hε
  have hφc : Continuous (Function.uncurry φ) := hφ.continuous
  have hψcont : Continuous (Function.uncurry ψ) := hψ.continuous
  set K : Set (E n) := Prod.fst '' tsupport (Function.uncurry ψ) with hKdef
  have hK : IsCompact K := hψc.isCompact.image continuous_fst
  have hKψ : ∀ x, x ∉ K → ∀ y, ψ x y = 0 := by
    intro x hx y
    by_contra h
    exact hx ⟨(x, y), subset_tsupport _ h, rfl⟩
  obtain ⟨C2, hC2, htay⟩ := taylor_bound φ hφ hK y₀
  obtain ⟨Lψ, hLip⟩ := hψ.lipschitzWith_of_hasCompactSupport hψc (by simp)
  obtain ⟨M, hM⟩ := hψcont.bounded_above_of_compact_support hψc
  have hM' : ∀ x y, ‖ψ x y‖ ≤ M := fun x y => hM (x, y)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM' 0 0)
  have hLip' : ∀ x y y', ‖ψ x y - ψ x y'‖ ≤ (Lψ : ℝ) * ‖y - y'‖ := by
    intro x y y'
    have := hLip.dist_le_mul (x, y) (x, y')
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_eq_norm, dist_eq_norm] at this
    exact this
  set c := 2 * Real.pi * C2 * M + Lψ with hc
  have hc0 : 0 ≤ c := by positivity
  set VK := (volume K).toReal with hVK
  have hVK0 : 0 ≤ VK := ENNReal.toReal_nonneg
  set β := (volume (ball (0 : E m) 1)).toReal + 1 with hβ
  have hβ0 : 0 ≤ β := by positivity
  set t := (1 / p).toReal with ht
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hs : (conjExp p)⁻¹.toReal = 1 - t := conjExp_inv_toReal hp
  set ε' := ε / (m + 2) with hε'
  obtain ⟨C, hC⟩ := hS ε' (by positivity)
  refine ⟨max C 0 + c * (VK + 1) * β, ?_⟩
  intro L hL g hgm ⟨B, hB⟩ hgs
  set R := L ^ (m + 2) with hRdef
  have hLR : L ≤ R := le_self_pow₀ hL (by omega)
  have hR1 : 1 ≤ R := hL.trans hLR
  have hR0 : 0 < R := by linarith
  set f : E m → ℂ := fun y => g (R • (y - y₀)) with hf
  have hfm : Measurable f := hgm.comp ((measurable_id.sub_const y₀).const_smul R)
  have hfMem : MemLp f p volume := by
    refine memLp_of_bdd hfm (fun y => hB _) (c := y₀) (r := L) ?_ p
    intro y hy
    apply hgs
    intro hmem
    apply hy
    rw [mem_closedBall, dist_eq_norm]
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR0] at hmem
    nlinarith [norm_nonneg (y - y₀)]
  have hgi : Integrable g := memLp_one_iff_integrable.mp (memLp_of_bdd hgm hB hgs 1)
  have hSf := eLpNorm_le_of_opNorm_le (hC R hR1) ENNReal.ofReal_ne_top hfMem
  rw [eLpNorm_comp_smul_sub hgm hR0.ne' y₀ p] at hSf
  have hSmeas := oscillatoryOp_stronglyMeasurable φ ψ hφc hψcont R hfm
  set κ := c * L ^ 2 / R * ∫ z, ‖g z‖ with hκ
  have hκ0 : 0 ≤ κ := by
    have : 0 ≤ ∫ z, ‖g z‖ := integral_nonneg fun z => norm_nonneg _
    positivity
  have hpt := pointwise_bound φ ψ hφc hψcont hKψ hC2 hM' hLip' Lψ.2 y₀ htay hL hLR hgi hgs
  have hhold := eLpNorm_one_le hgm.aestronglyMeasurable hL hgs hp
  have hint : ENNReal.ofReal (∫ z, ‖g z‖) = eLpNorm g 1 volume := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hgi, eLpNorm_one_eq_lintegral_enorm]
  have hLε : 1 ≤ L ^ ε := Real.one_le_rpow hL hε.le
  set X := eLpNorm g p volume with hX
  -- the main term
  have hmain : ENNReal.ofReal (R ^ m) * (ENNReal.ofReal (C * R ^ (-((m : ℝ) *
      (conjExp p)⁻¹.toReal) + ε')) * (ENNReal.ofReal |(R ^ m)⁻¹| ^ t * X)) ≤
        ENNReal.ofReal (max C 0 * L ^ ε) * X := by
    calc _ ≤ ENNReal.ofReal (R ^ m) * (ENNReal.ofReal (max C 0 * R ^ (-((m : ℝ) *
          (conjExp p)⁻¹.toReal) + ε')) * (ENNReal.ofReal |(R ^ m)⁻¹| ^ t * X)) := by
          gcongr
          exact le_max_left _ _
      _ = ENNReal.ofReal (R ^ m * (max C 0 * R ^ (-((m : ℝ) * (conjExp p)⁻¹.toReal) + ε')) *
          |(R ^ m)⁻¹| ^ t) * X := by
          have hD : 0 ≤ R ^ m * (max C 0 * R ^ (-((m : ℝ) * (conjExp p)⁻¹.toReal) + ε')) :=
            mul_nonneg (pow_nonneg hR0.le m) (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hR0.le _))
          rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) ht0, ENNReal.ofReal_mul hD,
            ENNReal.ofReal_mul (p := R ^ m) (pow_nonneg hR0.le m)]
          ring
      _ = ENNReal.ofReal (max C 0 * L ^ ε) * X := by
          rw [hs, scale_real hR0, hRdef, hε', pow_rpow_div (by linarith)]
  -- the error term
  have herr : ENNReal.ofReal κ * ENNReal.ofReal (VK + 1) ≤
      ENNReal.ofReal (c * (VK + 1) * β * L ^ ε) * X := by
    calc ENNReal.ofReal κ * ENNReal.ofReal (VK + 1)
        = ENNReal.ofReal (c * L ^ 2 / R) * ENNReal.ofReal (∫ z, ‖g z‖) *
            ENNReal.ofReal (VK + 1) := by
          rw [hκ, ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (c * L ^ 2 / R) * (X * ENNReal.ofReal (L ^ m * β)) *
            ENNReal.ofReal (VK + 1) := by
          rw [hint]
          gcongr
      _ = ENNReal.ofReal (c * L ^ 2 / R * (L ^ m * β) * (VK + 1)) * X := by
          rw [ENNReal.ofReal_mul (p := c * L ^ 2 / R * (L ^ m * β)) (by positivity),
            ENNReal.ofReal_mul (p := c * L ^ 2 / R) (by positivity)]
          ring
      _ ≤ ENNReal.ofReal (c * (VK + 1) * β * L ^ ε) * X := by
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
          have hL0 : 0 < L := by linarith
          have e : c * L ^ 2 / R * (L ^ m * β) * (VK + 1) = c * (VK + 1) * β := by
            rw [hRdef]
            field_simp
            ring
          rw [e]
          have : 0 ≤ c * (VK + 1) * β := by positivity
          nlinarith
  calc eLpNorm (linearizedRestriction φ ψ y₀ g) p volume
      ≤ eLpNorm ((R ^ m : ℝ) • (fun x => ‖oscillatoryOp φ ψ R f x‖) +
          K.indicator fun _ => κ) p volume :=
        eLpNorm_mono_real fun x => by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          exact hpt x
    _ ≤ eLpNorm ((R ^ m : ℝ) • (fun x => ‖oscillatoryOp φ ψ R f x‖)) p volume +
          eLpNorm (K.indicator fun _ => κ) p volume :=
        eLpNorm_add_le (hSmeas.norm.const_smul _).aestronglyMeasurable
          ((stronglyMeasurable_const.indicator hK.isClosed.measurableSet).aestronglyMeasurable) hp
    _ = ENNReal.ofReal (R ^ m) * eLpNorm (oscillatoryOp φ ψ R f) p volume +
          eLpNorm (K.indicator fun _ => κ) p volume := by
        rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_of_nonneg (by positivity)]
    _ ≤ ENNReal.ofReal (R ^ m) * (ENNReal.ofReal (C * R ^ (-((m : ℝ) *
          (conjExp p)⁻¹.toReal) + ε')) * (ENNReal.ofReal |(R ^ m)⁻¹| ^ t * X)) +
          ENNReal.ofReal κ * ENNReal.ofReal (VK + 1) := by
        gcongr
        exact eLpNorm_indicator_le hK hκ0 hp
    _ ≤ ENNReal.ofReal (max C 0 * L ^ ε) * X + ENNReal.ofReal (c * (VK + 1) * β * L ^ ε) * X :=
        add_le_add hmain herr
    _ = ENNReal.ofReal ((max C 0 + c * (VK + 1) * β) * L ^ ε) * X := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

end TaoBR.Tao49.PartL
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
alias local_estimate_of_oscillatoryOp_le := TaoBR.Tao49.PartL.local_estimate_of_oscillatoryOp_le

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartI
/-!
# Part I of the Theorem 4.9 Blueprint: `restrMu_muQ_of_local`

Change of weight from `|ψ|^p` to `|ψ|^q`. Instead of the dyadic decomposition of the Blueprint
docstring we use a single weighted interpolation. With `s = p/(p-1)`, `a(x) = |ψ(x, y₀)|`,
`Φ = Grad φ y₀`, let `T g (x) = a(x)^s ĝ(Φ(x))` on the measure `ν = a^{-s} dx` (density `⊤` where
`a = 0`, where `T g = 0`). Then
* `∫ |T g| dν = ∫_{a ≠ 0} |ĝ ∘ Φ| ≤ |K| ‖g‖₁` (`K` compact containing `{a ≠ 0}`),
* `∫ |T g|^p dν = ∫ a^{s(p-1)} |ĝ ∘ Φ|^p = ∫ a^p |ĝ ∘ Φ|^p = ‖ℜ_{y₀} g‖_p^p ≤ (C L^ε)^p ‖g‖_p^p`,
* so `interp_L1_Lp` gives `∫ a^{s(r-1)} |ĝ ∘ Φ|^r = ∫ |T g|^r dν ≲ (C L^ε)^{s(r-1)} ‖g‖_r^r`,
and `a^q ≤ M^{q - s(r-1)} a^{s(r-1)}` since `s(r-1) < q` (this is `r < 1 + q(1 - 1/p)`).
Finally `∫ |f̂|^r dμ_q = ∫ a^q |f̂ ∘ Φ|^r dx`, and `ε = α r/(s(r-1))`.
-/
/-! ## Generic facts -/
/-- The class of bounded measurable functions vanishing off `B(0, L)`. -/
def PL {m : ℕ} (L : ℝ) (g : E m → ℂ) : Prop :=
  Measurable g ∧ (∃ B : ℝ, ∀ y, ‖g y‖ ≤ B) ∧ ∀ y, y ∉ closedBall (0 : E m) L → g y = 0

lemma PL_integrable {m : ℕ} {L : ℝ} {g : E m → ℂ} (hg : PL L g) : Integrable g := by
  obtain ⟨hm, ⟨B, hB⟩, hz⟩ := hg
  have hon : IntegrableOn g (closedBall (0 : E m) L) := by
    refine ⟨hm.aestronglyMeasurable.restrict, ?_⟩
    exact .restrict_of_bounded (C := B) measure_closedBall_lt_top
      (Filter.Eventually.of_forall hB)
  exact hon.integrable_of_forall_notMem_eq_zero hz

lemma PL_hi {m : ℕ} {L : ℝ} {g : E m → ℂ} (hg : PL L g) (t : ℝ) :
    PL L (fun x => if t < ‖g x‖ then g x else 0) := by
  obtain ⟨hm, ⟨B, hB⟩, hz⟩ := hg
  refine ⟨Measurable.ite (measurableSet_lt measurable_const hm.norm) hm measurable_const,
    ⟨B, fun y => ?_⟩, fun y hy => ?_⟩
  · dsimp only
    split_ifs
    · exact hB y
    · simpa using (norm_nonneg _).trans (hB y)
  · simp [hz y hy]

lemma PL_lo {m : ℕ} {L : ℝ} {g : E m → ℂ} (hg : PL L g) (t : ℝ) :
    PL L (fun x => if t < ‖g x‖ then 0 else g x) := by
  obtain ⟨hm, ⟨B, hB⟩, hz⟩ := hg
  refine ⟨Measurable.ite (measurableSet_lt measurable_const hm.norm) measurable_const hm,
    ⟨B, fun y => ?_⟩, fun y hy => ?_⟩
  · dsimp only
    split_ifs
    · simpa using (norm_nonneg _).trans (hB y)
    · exact hB y
  · simp [hz y hy]

lemma fourier_add' {m : ℕ} {g g' : E m → ℂ} (hg : Integrable g) (hg' : Integrable g') :
    𝓕 (g + g') = 𝓕 g + 𝓕 g' := by
  funext ξ
  simp only [Real.fourier_eq, Pi.add_apply, smul_add]
  exact integral_add ((Real.fourierIntegral_convergent_iff ξ).2 hg)
    ((Real.fourierIntegral_convergent_iff ξ).2 hg')

lemma fourier_cont {m : ℕ} {g : E m → ℂ} (hg : Integrable g) : Continuous (𝓕 g) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hg

lemma enorm_fourier_le {m : ℕ} (g : E m → ℂ) (ξ : E m) :
    ‖𝓕 g ξ‖ₑ ≤ ∫⁻ y, ‖g y‖ₑ := by
  rw [Real.fourier_eq]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1; funext y
  rw [Circle.smul_def, smul_eq_mul, enorm_mul, ← ofReal_norm (𝐞 _ : ℂ), Circle.norm_coe,
    ENNReal.ofReal_one, one_mul]

lemma grad_cont {n m : ℕ} {φ : E n → E m → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (y₀ : E m) : Continuous (Grad φ y₀) := by
  have h : ContDiff ℝ 0 (fun x => fderiv ℝ (φ x) y₀) :=
    hφ.fderiv contDiff_const (by exact_mod_cast le_top)
  exact (InnerProductSpace.toDual ℝ (E m)).symm.continuous.comp h.continuous

/-- `∫⁻ ‖f‖^p ≤ c^p ∫⁻ ‖g‖^p` from an `eLpNorm` bound. -/
lemma lint_le_of_eLpNorm_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → ℂ} {g : β → ℂ} {p : ℝ} (hp : 0 < p) {c : ℝ≥0∞}
    (h : eLpNorm f (ENNReal.ofReal p) μ ≤ c * eLpNorm g (ENNReal.ofReal p) ν) :
    ∫⁻ x, ‖f x‖ₑ ^ p ∂μ ≤ c ^ p * ∫⁻ y, ‖g y‖ₑ ^ p ∂ν := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le] at h
  have h2 := ENNReal.rpow_le_rpow h hp.le
  rwa [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    one_div_mul_cancel hp.ne', ENNReal.rpow_one, ENNReal.rpow_one] at h2

/-- The converse: an `eLpNorm` bound from `∫⁻ ‖f‖^p ≤ c^p ∫⁻ ‖g‖^p`. -/
lemma eLpNorm_le_of_lint_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → ℂ} {g : β → ℂ} {p : ℝ} (hp : 0 < p) {c : ℝ≥0∞}
    (h : ∫⁻ x, ‖f x‖ₑ ^ p ∂μ ≤ c ^ p * ∫⁻ y, ‖g y‖ₑ ^ p ∂ν) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ c * eLpNorm g (ENNReal.ofReal p) ν := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  have h2 := ENNReal.rpow_le_rpow h (by positivity : 0 ≤ 1 / p)
  rwa [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hp.ne', ENNReal.rpow_one] at h2

/-! ## Pointwise weight algebra -/
lemma wpow {a F : ℝ≥0∞} (ha0 : a ≠ 0) (ha : a ≠ ⊤) {s r : ℝ} (hr : 0 ≤ r) :
    a ^ (-s) * (a ^ s * F) ^ r = a ^ (s * (r - 1)) * F ^ r := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr, ← ENNReal.rpow_mul, ← mul_assoc,
    ← ENNReal.rpow_add _ _ ha0 ha]
  congr 2; ring

lemma wpow_zero {F : ℝ≥0∞} {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    (0 : ℝ≥0∞) ^ (-s) * ((0 : ℝ≥0∞) ^ s * F) ^ r = 0 := by
  rw [ENNReal.zero_rpow_of_pos hs, zero_mul, ENNReal.zero_rpow_of_pos hr, mul_zero]

lemma wpow_one {a F : ℝ≥0∞} (ha : a ≠ ⊤) {s : ℝ} (hs : 0 < s) :
    a ^ (-s) * (a ^ s * F) ≤ F := by
  rcases eq_or_ne a 0 with h | h
  · subst h; rw [ENNReal.zero_rpow_of_pos hs, zero_mul, mul_zero]; exact zero_le
  · have := wpow (F := F) h ha (s := s) (r := 1) zero_le_one
    simp only [ENNReal.rpow_one, sub_self, mul_zero, ENNReal.rpow_zero, one_mul] at this
    rw [this]

lemma wpow_le {a F : ℝ≥0∞} {M : ℝ} (haM : a ≤ ENNReal.ofReal M) {s r q : ℝ} (hs : 0 < s)
    (hr : 0 < r) (hsq : s * (r - 1) ≤ q) (hq : 0 < q) :
    a ^ q * F ^ r ≤ ENNReal.ofReal (M ^ (q - s * (r - 1))) * (a ^ (-s) * (a ^ s * F) ^ r) := by
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top haM
  rcases eq_or_ne a 0 with h | h
  · subst h; rw [ENNReal.zero_rpow_of_pos hq, zero_mul]; exact zero_le
  have hM : 0 ≤ M := by
    by_contra hM; push Not at hM
    rw [ENNReal.ofReal_of_nonpos hM.le] at haM
    exact h (le_antisymm haM zero_le)
  rw [wpow h ha hr.le, ← mul_assoc]
  gcongr
  have e : a ^ q = a ^ (q - s * (r - 1)) * a ^ (s * (r - 1)) := by
    rw [← ENNReal.rpow_add _ _ h ha]; ring_nf
  rw [e, ← ENNReal.ofReal_rpow_of_nonneg hM (by linarith)]
  gcongr

/-! ## Exponent bookkeeping -/
lemma r_lt_p {p q r : ℝ} (hp : 1 < p) (hqp : q < p) (hr : r < 1 + q * (1 - 1 / p)) : r < p := by
  have h1 : 0 < 1 - 1 / p := by
    have : 1 / p < 1 := by rw [div_lt_one (by linarith)]; exact hp
    linarith
  have : q * (1 - 1 / p) < p * (1 - 1 / p) := mul_lt_mul_of_pos_right hqp h1
  have e : p * (1 - 1 / p) = p - 1 := by field_simp
  linarith

lemma s_r_lt_q {p q r : ℝ} (hp : 1 < p) (hr : r < 1 + q * (1 - 1 / p)) :
    p / (p - 1) * (r - 1) < q := by
  have hp1 : 0 < p - 1 := by linarith
  have e : 1 - 1 / p = (p - 1) / p := by field_simp
  rw [e] at hr
  have h2 : (r - 1) * p < q * (p - 1) := by
    have := sub_lt_iff_lt_add'.2 hr
    rw [mul_div_assoc'] at this
    rw [lt_div_iff₀ (by linarith)] at this
    linarith
  rw [div_mul_eq_mul_div, div_lt_iff₀ hp1]
  linarith

end TaoBR.Tao49.PartI
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartI
variable {n m : ℕ} (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ) (y₀ : E m)
/-! ## The main lemma -/
/-- The weighted operator `T g (x) = |ψ(x, y₀)|^s ĝ(Φ(x))`. -/
noncomputable def Tw (s : ℝ) (g : E m → ℂ) (x : E n) : ℂ :=
  ((‖ψ x y₀‖ ^ s : ℝ) : ℂ) * 𝓕 g (Grad φ y₀ x)

/-- The weight `|ψ(x, y₀)|^{-s}` (`⊤` where `ψ(x, y₀) = 0`). -/
noncomputable def wt (s : ℝ) (x : E n) : ℝ≥0∞ := ‖ψ x y₀‖ₑ ^ (-s)

lemma enorm_Tw {s : ℝ} (hs : 0 ≤ s) (g : E m → ℂ) (x : E n) :
    ‖Tw φ ψ y₀ s g x‖ₑ = ‖ψ x y₀‖ₑ ^ s * ‖𝓕 g (Grad φ y₀ x)‖ₑ := by
  rw [Tw, enorm_mul, ← ofReal_norm (((‖ψ x y₀‖ ^ s : ℝ) : ℂ)), Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs, ofReal_norm]

end TaoBR.Tao49.PartI
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartI
variable {n m : ℕ} (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ) (y₀ : E m)
variable {φ ψ}
lemma psi0_cont (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) :
    Continuous (fun x => ψ x y₀) :=
  hψ.continuous.comp (continuous_id.prodMk continuous_const)

lemma wt_meas (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (s : ℝ) :
    Measurable (wt ψ y₀ s) :=
  ((psi0_cont y₀ hψ).measurable.enorm).pow_const _

lemma Tw_meas (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) {s : ℝ} (hs : 0 ≤ s) {g : E m → ℂ}
    (hg : Integrable g) : Measurable (Tw φ ψ y₀ s g) := by
  have h1 : Continuous (fun x => ((‖ψ x y₀‖ ^ s : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((psi0_cont y₀ hψ).norm.rpow_const (fun _ => Or.inr hs))
  exact (h1.mul ((fourier_cont hg).comp (grad_cont hφ y₀))).measurable

lemma Tw_add {s : ℝ} {g g' : E m → ℂ} (hg : Integrable g) (hg' : Integrable g') :
    Tw φ ψ y₀ s (g + g') = Tw φ ψ y₀ s g + Tw φ ψ y₀ s g' := by
  funext x
  simp only [Tw, fourier_add' hg hg', Pi.add_apply, mul_add]

/-- A compact set outside which `ψ(·, y₀) = 0`. -/
lemma exists_compact (hψc : HasCompactSupport (Function.uncurry ψ)) :
    ∃ K : Set (E n), IsCompact K ∧ ∀ x, x ∉ K → ψ x y₀ = 0 := by
  refine ⟨Prod.fst '' tsupport (Function.uncurry ψ), hψc.isCompact.image continuous_fst,
    fun x hx => ?_⟩
  have : (x, y₀) ∉ tsupport (Function.uncurry ψ) := fun h => hx ⟨_, h, rfl⟩
  simpa using image_eq_zero_of_notMem_tsupport this

lemma exists_bound (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ))
    (hψc : HasCompactSupport (Function.uncurry ψ)) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ x, ‖ψ x y₀‖ ≤ M := by
  obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  exact ⟨max C 1, le_max_right _ _, fun x => (hC (x, y₀)).trans (le_max_left _ _)⟩

/-- The `L¹` bound. -/
lemma Tw_L1 {K : Set (E n)} (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ))
    (hK : ∀ x, x ∉ K → ψ x y₀ = 0) (hKm : MeasurableSet K) {s : ℝ} (hs : 0 < s)
    (g : E m → ℂ) :
    ∫⁻ x, ‖Tw φ ψ y₀ s g x‖ₑ ∂(volume.withDensity (wt ψ y₀ s)) ≤
      volume K * ∫⁻ y, ‖g y‖ₑ := by
  refine (lintegral_withDensity_le_lintegral_mul _ (wt_meas y₀ hψ s) _).trans ?_
  calc ∫⁻ x, (wt ψ y₀ s * fun x => ‖Tw φ ψ y₀ s g x‖ₑ) x
      ≤ ∫⁻ x, K.indicator (fun _ => ∫⁻ y, ‖g y‖ₑ) x := by
        refine lintegral_mono (fun x => ?_)
        simp only [Pi.mul_apply, wt]
        rw [enorm_Tw φ ψ y₀ hs.le]
        by_cases hx : x ∈ K
        · rw [indicator_of_mem hx]
          exact (wpow_one enorm_ne_top hs).trans (enorm_fourier_le _ _)
        · rw [hK x hx, enorm_zero, ENNReal.zero_rpow_of_pos hs, zero_mul, mul_zero]
          exact zero_le
    _ = volume K * ∫⁻ y, ‖g y‖ₑ := by rw [lintegral_indicator_const hKm, mul_comm]

/-- The `Lᵖ` bound: the weighted `Lᵖ` norm of `T g` is that of `ℜ_{y₀} g`. -/
lemma Tw_Lp (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) {s p : ℝ} (hs : 0 < s)
    (hp : 0 < p) (hsp : s * (p - 1) = p) (g : E m → ℂ) :
    ∫⁻ x, ‖Tw φ ψ y₀ s g x‖ₑ ^ p ∂(volume.withDensity (wt ψ y₀ s)) ≤
      ∫⁻ x, ‖linearizedRestriction φ ψ y₀ g x‖ₑ ^ p := by
  refine (lintegral_withDensity_le_lintegral_mul _ (wt_meas y₀ hψ s) _).trans ?_
  refine lintegral_mono (fun x => ?_)
  simp only [Pi.mul_apply, wt]
  rw [enorm_Tw φ ψ y₀ hs.le]
  rcases eq_or_ne ‖ψ x y₀‖ₑ 0 with h | h
  · rw [h, wpow_zero hs hp]; exact zero_le
  · rw [wpow h enorm_ne_top hp.le, hsp, linearizedRestriction, enorm_mul,
      ENNReal.mul_rpow_of_nonneg _ _ hp.le]
    rfl

/-- The pointwise comparison of the weights `|ψ|^q` and `|ψ|^{s(r-1)}`. -/
lemma weight_le {M : ℝ} (hM : ∀ x, ‖ψ x y₀‖ ≤ M) {s r q : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hsq : s * (r - 1) ≤ q) (hq : 0 < q) (g : E m → ℂ) (x : E n) :
    ‖ψ x y₀‖ₑ ^ q * ‖𝓕 g (Grad φ y₀ x)‖ₑ ^ r ≤
      ENNReal.ofReal (M ^ (q - s * (r - 1))) * (wt ψ y₀ s x * ‖Tw φ ψ y₀ s g x‖ₑ ^ r) := by
  rw [wt, enorm_Tw φ ψ y₀ hs.le]
  refine wpow_le ?_ hs hr hsq hq
  rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hM x)

end TaoBR.Tao49.PartI
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartI
lemma A0_pow {C' R ε p r s α : ℝ} (hC' : 0 < C') (hR : 0 < R) (hp : 1 < p)
    (hs : s = p / (p - 1)) (hθ : s * (r - 1) ≠ 0) (hε : ε = α * r / (s * (r - 1))) :
    ((C' * R ^ ε) ^ p) ^ ((r - 1) / (p - 1)) = C' ^ (s * (r - 1)) * (R ^ α) ^ r := by
  have e1 : p * ((r - 1) / (p - 1)) = s * (r - 1) := by rw [hs]; ring
  have e2 : ε * (s * (r - 1)) = α * r := by rw [hε, div_mul_cancel₀ _ hθ]
  rw [← Real.rpow_mul (by positivity), e1, Real.mul_rpow hC'.le (by positivity),
    ← Real.rpow_mul hR.le, e2, ← Real.rpow_mul hR.le]

lemma PL_schwartz {m : ℕ} {R : ℝ} (f : 𝓢(E m, ℂ)) (hf : tsupport f ⊆ closedBall 0 R) :
    PL R (f : E m → ℂ) := by
  have hc : HasCompactSupport (f : E m → ℂ) :=
    (isCompact_closedBall (0 : E m) R).of_isClosed_subset (isClosed_tsupport _) hf
  exact ⟨f.continuous.measurable, f.continuous.bounded_above_of_compact_support hc,
    fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hf h))⟩

theorem restrMu_muQ_of_local {n m : ℕ} (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (y₀ : E m) {p q r : ℝ} (hp : 1 < p) (hq : 1 ≤ q) (hqp : q < p) (hqr : q < r)
    (hr : r < 1 + q * (1 - 1 / p))
    (hL : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ L : ℝ, 1 ≤ L → ∀ g : E m → ℂ, Measurable g →
      (∃ B : ℝ, ∀ y, ‖g y‖ ≤ B) → (∀ y, y ∉ closedBall (0 : E m) L → g y = 0) →
        eLpNorm (linearizedRestriction φ ψ y₀ g) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * L ^ ε) * eLpNorm g (ENNReal.ofReal p) volume) :
    ∀ α : ℝ, 0 < α → RestrMu (muQ φ ψ y₀ q) r α := by
  intro α hα
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hr1 : 1 < r := by linarith
  have hr0 : 0 < r := by linarith
  have hrp : r < p := r_lt_p hp hqp hr
  set s := p / (p - 1) with hs_def
  have hs : 0 < s := div_pos hp0 (by linarith)
  have hθ : s * (r - 1) < q := s_r_lt_q hp hr
  have hθ0 : 0 < s * (r - 1) := mul_pos hs (by linarith)
  have hsp : s * (p - 1) = p := by rw [hs_def, div_mul_cancel₀ _ (by linarith : p - 1 ≠ 0)]
  obtain ⟨K, hKc, hK⟩ := exists_compact y₀ hψc
  obtain ⟨M, hM1, hM⟩ := exists_bound y₀ hψ hψc
  set ε := α * r / (s * (r - 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨C, hC⟩ := hL ε hε0
  set C' := max C 1 with hC'
  have hC'0 : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set A₁ := (volume K).toReal + 1 with hA₁def
  have hA₁ : 0 < A₁ := by positivity
  have hKA : volume K ≤ ENNReal.ofReal A₁ := by
    rw [← ENNReal.ofReal_toReal hKc.measure_lt_top.ne]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  set c0 := 2 * r * (2 / (r - 1) + 2 ^ p / (p - r)) with hc0
  have hc00 : 0 ≤ c0 := by
    have : 0 < r - 1 := by linarith
    have : 0 < p - r := by linarith
    positivity
  set Kc := M ^ (q - s * (r - 1)) * (c0 * A₁ ^ ((p - r) / (p - 1)) * C' ^ (s * (r - 1)))
    with hKc_def
  have hKc0 : 0 ≤ Kc := by positivity
  refine ⟨Real.toNNReal (Kc ^ (1 / r)), fun R hR f hf => ?_⟩
  have hR0 : 0 < R := by linarith
  have hPf : PL R (f : E m → ℂ) := PL_schwartz f hf
  set ν := volume.withDensity (wt ψ y₀ s) with hν
  set A₀ := (C' * R ^ ε) ^ p with hA₀def
  have hA₀ : 0 < A₀ := by positivity
  have h1 : ∀ g, PL R g → ∫⁻ x, ‖Tw φ ψ y₀ s g x‖ₑ ∂ν ≤
      ENNReal.ofReal A₁ * ∫⁻ y, ‖g y‖ₑ := fun g _ =>
    (Tw_L1 y₀ hψ hK hKc.measurableSet hs g).trans (by gcongr)
  have h0 : ∀ g, PL R g → ∫⁻ x, ‖Tw φ ψ y₀ s g x‖ₑ ^ p ∂ν ≤
      ENNReal.ofReal A₀ * ∫⁻ y, ‖g y‖ₑ ^ p := by
    intro g hg
    refine (Tw_Lp y₀ hψ hs hp0 hsp g).trans ?_
    have h' : eLpNorm (linearizedRestriction φ ψ y₀ g) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C' * R ^ ε) * eLpNorm g (ENNReal.ofReal p) volume := by
      refine (hC R hR g hg.1 hg.2.1 hg.2.2).trans ?_
      gcongr
      exact le_max_left _ _
    have := lint_le_of_eLpNorm_le hp0 h'
    rwa [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le] at this
  have hI := interp_L1_Lp volume ν (PL R) (Tw φ ψ y₀ s) (fun g t hg => PL_hi hg t)
    (fun g t hg => PL_lo hg t)
    (fun g g' hg hg' => Tw_add y₀ (PL_integrable hg) (PL_integrable hg'))
    (fun g hg => Tw_meas y₀ hφ hψ hs.le (PL_integrable hg)) (fun g hg => hg.1) hp hA₁ hA₀
    h1 h0 hr1 hrp f hPf
  rw [A0_pow hC'0 hR0 hp hs_def hθ0.ne' hε] at hI
  have hfi := PL_integrable hPf
  have hFm : Measurable (fun ξ => ‖𝓕 (f : E m → ℂ) ξ‖ₑ ^ r) :=
    (fourier_cont hfi).measurable.enorm.pow_const r
  have hdm : Measurable (fun x => ‖ψ x y₀‖ₑ ^ q) :=
    (psi0_cont y₀ hψ).measurable.enorm.pow_const q
  have hTm : Measurable (fun x => ‖Tw φ ψ y₀ s f x‖ₑ ^ r) :=
    (Tw_meas y₀ hφ hψ hs.le hfi).enorm.pow_const r
  apply eLpNorm_le_of_lint_le hr0
  rw [muQ, lintegral_map hFm (grad_cont hφ y₀).measurable,
    lintegral_withDensity_eq_lintegral_mul _ hdm
      (g := fun x => ‖𝓕 (f : E m → ℂ) (Grad φ y₀ x)‖ₑ ^ r) (hFm.comp (grad_cont hφ y₀).measurable)]
  calc _
      ≤ ∫⁻ x, ENNReal.ofReal (M ^ (q - s * (r - 1))) *
          (wt ψ y₀ s x * ‖Tw φ ψ y₀ s f x‖ₑ ^ r) := by
        refine lintegral_mono (fun x => ?_)
        exact weight_le y₀ hM hs hr0 hθ.le hq0 f x
    _ = ENNReal.ofReal (M ^ (q - s * (r - 1))) * ∫⁻ x, ‖Tw φ ψ y₀ s f x‖ₑ ^ r ∂ν := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hν,
          lintegral_withDensity_eq_lintegral_mul _ (wt_meas y₀ hψ s) hTm]
        rfl
    _ ≤ ENNReal.ofReal (M ^ (q - s * (r - 1))) *
          (ENNReal.ofReal (c0 * A₁ ^ ((p - r) / (p - 1)) * (C' ^ (s * (r - 1)) * (R ^ α) ^ r)) *
            ∫⁻ y, ‖f y‖ₑ ^ r) := by
        gcongr
    _ = (((Real.toNNReal (Kc ^ (1 / r)) : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (R ^ α)) ^ r *
          ∫⁻ y, ‖f y‖ₑ ^ r := by
        rw [show (((Real.toNNReal (Kc ^ (1 / r)) : ℝ≥0) : ℝ≥0∞)) = ENNReal.ofReal (Kc ^ (1 / r))
          from rfl, ← ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hr0.le, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hKc0,
          one_div_mul_cancel hr0.ne', Real.rpow_one, hKc_def]
        ring

end TaoBR.Tao49.PartI
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
alias restrMu_muQ_of_local := TaoBR.Tao49.PartI.restrMu_muQ_of_local

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartN
open Filter
open scoped Topology Real
/-!
# Part N of the Theorem 4.9 Blueprint: normalization, decay, and the conclusion
-/
/-! ## Dilations -/
theorem continuous_fourier_schwartz {n : ℕ} (f : 𝓢(E n, ℂ)) : Continuous (𝓕 (f : E n → ℂ)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simpa using (continuous_inner : Continuous fun p : E n × E n => ⟪p.1, p.2⟫)) f.integrable

theorem eLpNorm_comp_smul {m : ℕ} {g : E m → ℂ} (hg : AEStronglyMeasurable g volume) {R : ℝ}
    (hR : R ≠ 0) (p : ℝ≥0∞) :
    eLpNorm (fun y => g (R • y)) p volume =
      ENNReal.ofReal |(R ^ m)⁻¹| ^ (1 / p).toReal * eLpNorm g p volume := by
  have h2 : eLpNorm (fun y => g (R • y)) p volume =
      eLpNorm g p (Measure.map (fun y : E m => R • y) volume) := by
    rw [eLpNorm_map_measure _ (measurable_const_smul R).aemeasurable]
    · rfl
    · rw [Measure.map_addHaar_smul volume hR]
      exact hg.smul_measure _
  rw [h2, Measure.map_addHaar_smul volume hR, finrank_euclideanSpace_fin,
    eLpNorm_smul_measure_of_ne_zero, smul_eq_mul]
  simp [hR]

theorem hasCompactSupport_of_tsupport {m : ℕ} {f : E m → ℂ} {R : ℝ}
    (hf : tsupport f ⊆ closedBall 0 R) : HasCompactSupport f :=
  (isCompact_closedBall 0 R).of_isClosed_subset (isClosed_tsupport _) hf

/-- The dilate `y ↦ a^m f(a y)`. -/
theorem exists_dilate {m : ℕ} {a : ℝ} (ha : 0 < a) (f : 𝓢(E m, ℂ)) {R : ℝ}
    (hf : tsupport f ⊆ closedBall 0 R) (p : ℝ≥0∞) :
    ∃ g : 𝓢(E m, ℂ), tsupport g ⊆ closedBall 0 (a⁻¹ * R) ∧
      (∀ ξ, 𝓕 (g : E m → ℂ) ξ = 𝓕 (f : E m → ℂ) (a⁻¹ • ξ)) ∧
      eLpNorm g p volume = ENNReal.ofReal (a ^ m) *
        (ENNReal.ofReal |(a ^ m)⁻¹| ^ (1 / p).toReal * eLpNorm f p volume) := by
  have hcs : HasCompactSupport fun y : E m => ((a ^ m : ℝ) : ℂ) * f (a • y) := by
    apply HasCompactSupport.mul_left
    have hf' := hasCompactSupport_of_tsupport hf
    exact hf'.comp_isClosedEmbedding
      (Homeomorph.smulOfNeZero a ha.ne').isClosedEmbedding
  have hsm : ContDiff ℝ (⊤ : ℕ∞) fun y : E m => ((a ^ m : ℝ) : ℂ) * f (a • y) :=
    contDiff_const.mul ((f.smooth ⊤).comp (contDiff_const_smul a))
  have h' : ∀ y : E m, (hcs.toSchwartzMap hsm) y = ((a ^ m : ℝ) : ℂ) * f (a • y) :=
    fun y => rfl
  refine ⟨hcs.toSchwartzMap hsm, ?_, ?_, ?_⟩
  · apply closure_minimal _ isClosed_closedBall
    intro y hy
    have hy' : f (a • y) ≠ 0 := fun h => hy (by rw [h', h, mul_zero])
    have h1 : a • y ∈ closedBall (0 : E m) R := hf (subset_tsupport _ hy')
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg ha.le] at h1
    rw [mem_closedBall, dist_zero_right]
    rw [← le_div_iff₀' ha] at h1
    rwa [div_eq_inv_mul] at h1
  · intro ξ
    simp only [Real.fourier_eq]
    have h := Measure.integral_comp_smul (volume : Measure (E m))
      (fun z => 𝐞 (-⟪a⁻¹ • z, ξ⟫) • (((a ^ m : ℝ) : ℂ) * f z)) a
    rw [finrank_euclideanSpace_fin] at h
    simp_rw [inv_smul_smul₀ ha.ne'] at h
    simp_rw [h']
    rw [h]
    have hfun : (fun x : E m => 𝐞 (-⟪a⁻¹ • x, ξ⟫) • (((a ^ m : ℝ) : ℂ) * f x)) =
        fun x => ((a ^ m : ℝ) : ℂ) * (𝐞 (-⟪a⁻¹ • x, ξ⟫) • f x) := by
      ext x; exact (mul_smul_comm _ _ _).symm
    rw [hfun, integral_const_mul, ← smul_mul_assoc]
    have hk : |(a ^ m)⁻¹| • ((a ^ m : ℝ) : ℂ) = 1 := by
      rw [abs_of_pos (by positivity), Complex.real_smul, ← Complex.ofReal_mul,
        inv_mul_cancel₀ (by positivity), Complex.ofReal_one]
    rw [hk, one_mul]
    congr 1; ext z
    rw [real_inner_smul_left, real_inner_smul_right]
  · have h'' : ((hcs.toSchwartzMap hsm) : E m → ℂ) =
        ((a ^ m : ℝ) : ℂ) • fun y => f (a • y) := by
      ext y; rfl
    rw [h'', eLpNorm_const_smul, eLpNorm_comp_smul f.continuous.aestronglyMeasurable ha.ne']
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

theorem enorm_rpow_ne_top {m : ℕ} (a : ℝ) (p : ℝ≥0∞) :
    ENNReal.ofReal (a ^ m) * ENNReal.ofReal |(a ^ m)⁻¹| ^ (1 / p).toReal ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)

theorem eLpNorm_scaleM {m : ℕ} {μ : Measure (E m)} {lam : ℝ} (F : E m → ℂ) (hF : Continuous F)
    (p : ℝ≥0∞) :
    eLpNorm F p (scaleM lam μ) = eLpNorm (fun ξ => F (lam⁻¹ • ξ)) p μ :=
  eLpNorm_map_measure hF.aestronglyMeasurable (measurable_const_smul _).aemeasurable

theorem restrMu_scale_of_restrMu {m : ℕ} {μ : Measure (E m)} {lam : ℝ} (hlam : 1 ≤ lam)
    {r α : ℝ} (hr : 1 ≤ r) (h : RestrMu μ r α) : RestrMu (scaleM lam μ) r α := by
  obtain ⟨C, hC⟩ := h
  have hl0 : 0 < lam := by linarith
  set K := ENNReal.ofReal (lam ^ m) * ENNReal.ofReal |(lam ^ m)⁻¹| ^ (1 / ENNReal.ofReal r).toReal
  have hK : K ≠ ⊤ := enorm_rpow_ne_top (m := m) lam _
  refine ⟨C * K.toNNReal, fun R hR f hf => ?_⟩
  obtain ⟨g, hgs, hgF, hgn⟩ := exists_dilate hl0 f hf (ENNReal.ofReal r)
  have hsub : closedBall (0 : E m) (lam⁻¹ * R) ⊆ closedBall 0 R := by
    apply closedBall_subset_closedBall
    have : lam⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlam
    nlinarith
  rw [eLpNorm_scaleM _ (continuous_fourier_schwartz f)]
  have : (fun ξ => 𝓕 (f : E m → ℂ) (lam⁻¹ • ξ)) = 𝓕 (g : E m → ℂ) := by
    ext ξ; rw [hgF]
  rw [this]
  refine (hC R hR g (hgs.trans hsub)).trans (le_of_eq ?_)
  rw [hgn, ENNReal.coe_mul, ENNReal.coe_toNNReal hK, ← mul_assoc]
  ring

end TaoBR.Tao49.PartN
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
alias restrMu_scale_of_restrMu := TaoBR.Tao49.PartN.restrMu_scale_of_restrMu

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartN
open Filter
open scoped Topology Real
theorem restrMu_of_restrMu_scale {m : ℕ} {μ : Measure (E m)} {lam : ℝ} (hlam : 1 ≤ lam)
    {q : ℝ} (hq : 1 ≤ q) (h : RestrMu (scaleM lam μ) q 0) : RestrMu μ q 0 := by
  obtain ⟨C, hC⟩ := h
  have hl0 : 0 < lam := by linarith
  have hi0 : 0 < lam⁻¹ := inv_pos.2 hl0
  set K := ENNReal.ofReal (lam⁻¹ ^ m) *
    ENNReal.ofReal |(lam⁻¹ ^ m)⁻¹| ^ (1 / ENNReal.ofReal q).toReal
  have hK : K ≠ ⊤ := enorm_rpow_ne_top (m := m) lam⁻¹ _
  refine ⟨C * K.toNNReal, fun R hR f hf => ?_⟩
  obtain ⟨g, hgs, hgF, hgn⟩ := exists_dilate hi0 f hf (ENNReal.ofReal q)
  rw [inv_inv] at hgs
  have hR' : 1 ≤ lam * R := by nlinarith
  have : 𝓕 (f : E m → ℂ) = fun ξ => 𝓕 (g : E m → ℂ) (lam⁻¹ • ξ) := by
    ext ξ; rw [hgF, inv_inv, smul_smul, mul_inv_cancel₀ hl0.ne', one_smul]
  rw [this, ← eLpNorm_scaleM _ (continuous_fourier_schwartz g)]
  refine (hC (lam * R) hR' g hgs).trans (le_of_eq ?_)
  rw [hgn, ENNReal.coe_mul, ENNReal.coe_toNNReal hK, Real.rpow_zero, ENNReal.ofReal_one,
    Real.rpow_zero, ENNReal.ofReal_one]
  ring

end TaoBR.Tao49.PartN
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
alias restrMu_of_restrMu_scale := TaoBR.Tao49.PartN.restrMu_of_restrMu_scale

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartN
open Filter
open scoped Topology Real
theorem continuous_fderiv_y {n m : ℕ} {φ : E n → E m → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ)) (y₀ : E m) :
    Continuous fun x => fderiv ℝ (fun y => φ x y) y₀ := by
  have h : ContDiff ℝ 0 (fun x => fderiv ℝ (fun y => φ x y) ((fun _ : E n => y₀) x)) :=
    ContDiff.fderiv (f := φ) hφ contDiff_const (by norm_cast)
  exact h.continuous

theorem continuous_Grad {n m : ℕ} {φ : E n → E m → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ)) (y₀ : E m) : Continuous (Grad φ y₀) :=
  (InnerProductSpace.toDual ℝ (E m)).symm.continuous.comp (continuous_fderiv_y hφ y₀)

theorem continuous_psi {n m : ℕ} {ψ : E n → E m → ℂ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (y₀ : E m) : Continuous fun x => ψ x y₀ :=
  hψ.continuous.comp (continuous_id.prodMk continuous_const)

theorem measurable_dens {n m : ℕ} {ψ : E n → E m → ℂ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (y₀ : E m) (q : ℝ) :
    Measurable fun x => ‖ψ x y₀‖ₑ ^ q :=
  ((continuous_psi hψ y₀).measurable.enorm).pow_const q

theorem lintegral_muQ {n m : ℕ} {φ : E n → E m → ℝ} {ψ : E n → E m → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (y₀ : E m) (q : ℝ)
    {F : E m → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ξ, F ξ ∂(muQ φ ψ y₀ q) = ∫⁻ x, ‖ψ x y₀‖ₑ ^ q * F (Grad φ y₀ x) := by
  unfold muQ
  rw [lintegral_map hF (continuous_Grad hφ y₀).measurable]
  exact lintegral_withDensity_eq_lintegral_mul _ (measurable_dens hψ y₀ q)
    (hF.comp (continuous_Grad hφ y₀).measurable)

theorem eLpNorm_linearizedRestriction {n m : ℕ} {φ : E n → E m → ℝ} {ψ : E n → E m → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (y₀ : E m) {q : ℝ} (hq : 1 ≤ q)
    {F : E m → ℂ} (hF : Continuous F) :
    eLpNorm (fun x => ψ x y₀ * F (gradient (fun y => φ x y) y₀)) (ENNReal.ofReal q) volume =
      eLpNorm F (ENNReal.ofReal q) (muQ φ ψ y₀ q) := by
  have hq0 : ENNReal.ofReal q ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ q),
    lintegral_muQ hφ hψ y₀ q (hF.measurable.enorm.pow_const q)]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ q)]
  rfl

/-! ## Cutoffs (as `parabolic_of_restrMu` in `proofs/parab/PartI.lean`) -/
/-- The cutoff `χ_k`: `1` on `closedBall 0 (k+1)`, supported in `closedBall 0 (2(k+1))`. -/
noncomputable def cut (m k : ℕ) : ContDiffBump (0 : E m) :=
  ⟨(k : ℝ) + 1, 2 * ((k : ℝ) + 1), by positivity, by linarith⟩

theorem cutC_hasCompactSupport {m : ℕ} (k : ℕ) :
    HasCompactSupport fun x : E m => ((cut m k x : ℝ) : ℂ) :=
  (cut m k).hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero

/-- `f_k = χ_k f`. -/
noncomputable def fk {m : ℕ} (f : 𝓢(E m, ℂ)) (k : ℕ) : 𝓢(E m, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun x => ((cut m k x : ℝ) : ℂ) * f x)
    ((cutC_hasCompactSupport k).mul_right)
    ((Complex.ofRealCLM.contDiff.comp (cut m k).contDiff).mul (f.smooth ⊤))

theorem fk_apply {m : ℕ} (f : 𝓢(E m, ℂ)) (k : ℕ) (x : E m) :
    fk f k x = ((cut m k x : ℝ) : ℂ) * f x := rfl

theorem tsupport_fk {m : ℕ} (f : 𝓢(E m, ℂ)) (k : ℕ) :
    tsupport (fk f k : E m → ℂ) ⊆ closedBall 0 (2 * ((k : ℝ) + 1)) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  rw [Function.mem_support, fk_apply] at hx
  have h1 : cut m k x ≠ 0 := fun h => hx (by simp [h])
  have h2 : x ∈ Function.support (cut m k) := h1
  rw [(cut m k).support_eq] at h2
  exact ball_subset_closedBall h2

theorem norm_fk_le {m : ℕ} (f : 𝓢(E m, ℂ)) (k : ℕ) (x : E m) : ‖fk f k x‖ ≤ ‖f x‖ := by
  rw [fk_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (cut m k).nonneg]
  exact mul_le_of_le_one_left (norm_nonneg _) (cut m k).le_one

theorem fk_eventually {m : ℕ} (f : 𝓢(E m, ℂ)) (x : E m) :
    ∀ᶠ k in atTop, fk f k x = f x := by
  filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with k hk
  have h1 : ‖x‖ ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hx : x ∈ closedBall (0 : E m) (cut m k).rIn := by
    rw [mem_closedBall, dist_zero_right]
    change ‖x‖ ≤ (k : ℝ) + 1
    linarith
  rw [fk_apply, (cut m k).one_of_mem_closedBall hx]
  simp

theorem tendsto_fourier_fk {m : ℕ} (f : 𝓢(E m, ℂ)) (ξ : E m) :
    Tendsto (fun k => 𝓕 (fk f k : E m → ℂ) ξ) atTop (𝓝 (𝓕 (f : E m → ℂ) ξ)) := by
  simp only [Real.fourier_eq]
  refine tendsto_integral_of_dominated_convergence (fun v => ‖f v‖) (fun k => ?_)
    f.integrable.norm (fun k => ae_of_all _ fun v => ?_) (ae_of_all _ fun v => ?_)
  · exact (Continuous.smul (by fun_prop) (fk f k).continuous).aestronglyMeasurable
  · rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
    exact norm_fk_le f k v
  · exact tendsto_const_nhds.congr' ((fk_eventually f v).mono fun k hk => by simp only [hk])

theorem conclusion_of_restrMu {n m : ℕ} (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (y₀ : E m) {q : ℝ} (hq : 1 ≤ q) (h : RestrMu (muQ φ ψ y₀ q) q 0) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(E m, ℂ),
      eLpNorm (linearizedRestriction φ ψ y₀ f) (ENNReal.ofReal q) volume ≤
        C * eLpNorm f (ENNReal.ofReal q) volume := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun f => ?_⟩
  have hk : ∀ k : ℕ, eLpNorm (linearizedRestriction φ ψ y₀ (fk f k)) (ENNReal.ofReal q)
      volume ≤ C * eLpNorm f (ENNReal.ofReal q) volume := by
    intro k
    calc _ = eLpNorm (𝓕 (fk f k : E m → ℂ)) (ENNReal.ofReal q) (muQ φ ψ y₀ q) :=
          eLpNorm_linearizedRestriction hφ hψ y₀ hq (continuous_fourier_schwartz _)
      _ ≤ C * ENNReal.ofReal ((2 * ((k : ℝ) + 1)) ^ (0 : ℝ)) *
            eLpNorm (fk f k) (ENNReal.ofReal q) volume :=
          hC _ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) _ (tsupport_fk f k)
      _ ≤ C * eLpNorm f (ENNReal.ofReal q) volume := by
          rw [Real.rpow_zero, ENNReal.ofReal_one, mul_one]
          gcongr 1
          exact eLpNorm_mono (norm_fk_le f k)
  have hcont : ∀ g : 𝓢(E m, ℂ), Continuous (linearizedRestriction φ ψ y₀ g) := fun g =>
    (continuous_psi hψ y₀).mul ((continuous_fourier_schwartz g).comp (continuous_Grad hφ y₀))
  calc _ ≤ atTop.liminf fun k => eLpNorm (linearizedRestriction φ ψ y₀ (fk f k))
          (ENNReal.ofReal q) volume :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun k => (hcont (fk f k)).aestronglyMeasurable)
          _ (ae_of_all _ fun x =>
            tendsto_const_nhds.mul (tendsto_fourier_fk f _))
    _ ≤ atTop.liminf fun _ : ℕ => C * eLpNorm f (ENNReal.ofReal q) volume :=
        liminf_le_liminf (Eventually.of_forall hk)
    _ = _ := liminf_const _

/-! ## Normalization and decay -/
theorem psi_slice_support {n m : ℕ} {ψ : E n → E m → ℂ}
    (hψc : HasCompactSupport (Function.uncurry ψ)) (y₀ : E m) :
    ∃ K : Set (E n), IsCompact K ∧ ∀ x, ψ x y₀ ≠ 0 → x ∈ K := by
  refine ⟨Prod.fst '' tsupport (Function.uncurry ψ), hψc.image continuous_fst, fun x hx => ?_⟩
  exact ⟨(x, y₀), subset_tsupport _ hx, rfl⟩

theorem lintegral_dens_ne_top {n m : ℕ} {ψ : E n → E m → ℂ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (y₀ : E m) {q : ℝ} (hq : 0 < q) :
    ∫⁻ x, ‖ψ x y₀‖ₑ ^ q ≠ ⊤ := by
  obtain ⟨K, hK, hKs⟩ := psi_slice_support hψc y₀
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuous_psi hψ y₀).continuousOn
  have hle : ∀ x, ‖ψ x y₀‖ₑ ^ q ≤ K.indicator (fun _ => ENNReal.ofReal B ^ q) x := by
    intro x
    by_cases hx : ψ x y₀ = 0
    · rw [hx, enorm_zero, ENNReal.zero_rpow_of_pos hq]; exact zero_le
    · rw [indicator_of_mem (hKs x hx)]
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB x (hKs x hx))
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_indicator_const hK.measurableSet]
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
    hK.measure_lt_top.ne

theorem isFiniteMeasure_muQ {n m : ℕ} {φ : E n → E m → ℝ} {ψ : E n → E m → ℂ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (y₀ : E m) {q : ℝ} (hq : 0 < q) : IsFiniteMeasure (muQ φ ψ y₀ q) := by
  have : IsFiniteMeasure ((volume : Measure (E n)).withDensity fun x => ‖ψ x y₀‖ₑ ^ q) :=
    isFiniteMeasure_withDensity (lintegral_dens_ne_top hψ hψc y₀ hq)
  unfold muQ; infer_instance

theorem ftMeasure_scaleM_muQ {n m : ℕ} {φ : E n → E m → ℝ} {ψ : E n → E m → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (y₀ : E m) {q : ℝ} (hq : 0 ≤ q) (lam : ℝ)
    (x : E m) :
    ftMeasure (scaleM lam (muQ φ ψ y₀ q)) x =
      ∫ z, Complex.exp (-(2 * Real.pi * Complex.I *
          (inner ℝ (lam⁻¹ • x) (gradient (fun y => φ z y) y₀) : ℝ))) *
        ((‖ψ z y₀‖ ^ q : ℝ) : ℂ) := by
  unfold ftMeasure scaleM muQ
  have hΦ := (continuous_Grad hφ y₀).measurable
  rw [Measure.map_map (measurable_const_smul _) hΦ,
    integral_map ((measurable_const_smul _).comp hΦ).aemeasurable
      (by fun_prop : Continuous fun ξ : E m => (𝐞 (-⟪ξ, x⟫) : ℂ)).aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (measurable_dens hψ y₀ q)
      (ae_of_all _ fun z => ENNReal.rpow_lt_top_of_nonneg hq enorm_ne_top)]
  congr 1; ext z
  have h1 : (‖ψ z y₀‖ₑ ^ q).toReal = ‖ψ z y₀‖ ^ q := by
    rw [← ENNReal.toReal_rpow, toReal_enorm]
  have h2 : ((𝐞 (-⟪((fun x => lam⁻¹ • x) ∘ Grad φ y₀) z, x⟫) : Circle) : ℂ) =
      Complex.exp (-(2 * Real.pi * Complex.I *
        (inner ℝ (lam⁻¹ • x) (gradient (fun y => φ z y) y₀) : ℝ))) := by
    rw [Real.fourierChar_apply]
    simp only [Function.comp, Grad, real_inner_smul_right, real_inner_comm]
    congr 1
    push_cast
    ring
  rw [h1, h2, Complex.real_smul, mul_comm]

theorem decay_scale {C c lam : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hlam : 1 ≤ lam) {m : ℕ} (x : E m) :
    C * (1 + ‖lam⁻¹ • x‖) ^ (-c) ≤ C * lam ^ c * (1 + ‖x‖) ^ (-c) := by
  have hl0 : 0 < lam := by linarith
  have h1 : (1 + ‖x‖) / lam ≤ 1 + ‖lam⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hl0.le), add_div, ← div_eq_inv_mul]
    gcongr
    exact div_le_self zero_le_one hlam
  have h2 := Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith : -c ≤ 0)
  rw [Real.div_rpow (by positivity) hl0.le, Real.rpow_neg hl0.le, div_inv_eq_mul] at h2
  rw [mul_assoc]
  gcongr
  linarith [mul_comm ((1 + ‖x‖) ^ (-c)) (lam ^ c)]

theorem exists_scale_decayMeasure {n m : ℕ} (hnm : m - 1 ≤ n) (hmn : n ≤ m)
    (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (hrank : HasConstantRank φ ψ (m - 1)) (p : ℝ≥0∞) (hp : 1 < p)
    (hS : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      opNorm p p (oscillatoryOp φ ψ R) ≤
        ENNReal.ofReal (C * R ^ (-((m : ℝ) * (conjExp p)⁻¹.toReal) + ε)))
    (y₀ : E m) (q : ℝ) (hq : 1 ≤ q) (hqp : ENNReal.ofReal q < p) :
    ∃ lam : ℝ, 1 ≤ lam ∧ DecayMeasure (scaleM lam (muQ φ ψ y₀ q)) (closedBall 0 (3 / 2)) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨K, hK, hKs⟩ := psi_slice_support hψc y₀
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (continuous_Grad hφ y₀).continuousOn
  set lam := max 1 M with hlam
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hl0 : 0 < lam := by linarith
  obtain ⟨C, c, hc, hC⟩ := TaoBR.linearizedMeasure_fourier_decay_of_oscillatoryOp_le n m hnm hmn
    φ ψ hφ hψ hψc hrank p hp hS y₀ q hq hqp
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 0)
    simpa using h
  have hfin := isFiniteMeasure_muQ (φ := φ) hψ hψc y₀ hq0
  refine ⟨lam, hlam1, ⟨?_, ?_, subset_rfl, ⟨C * lam ^ c, c, hc, fun x => ?_⟩⟩⟩
  · unfold scaleM; infer_instance
  · have hΦ := (continuous_Grad hφ y₀).measurable
    have hs : MeasurableSet (closedBall (0 : E m) (3 / 2))ᶜ := measurableSet_closedBall.compl
    unfold scaleM muQ
    rw [Measure.map_map (measurable_const_smul _) hΦ,
      Measure.map_apply ((measurable_const_smul _).comp hΦ) hs,
      withDensity_apply _ (((measurable_const_smul _).comp hΦ) hs)]
    have : ∀ z ∈ ((fun ξ : E m => lam⁻¹ • ξ) ∘ Grad φ y₀) ⁻¹' (closedBall (0 : E m) (3 / 2))ᶜ,
        ‖ψ z y₀‖ₑ ^ q = 0 := by
      intro z hz
      by_contra hne
      have hψz : ψ z y₀ ≠ 0 := fun h => hne (by rw [h, enorm_zero, ENNReal.zero_rpow_of_pos hq0])
      apply hz
      rw [mem_closedBall, dist_zero_right, Function.comp, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.2 hl0.le)]
      have h1 : ‖Grad φ y₀ z‖ ≤ lam := (hM z (hKs z hψz)).trans (le_max_right _ _)
      calc lam⁻¹ * ‖Grad φ y₀ z‖ ≤ lam⁻¹ * lam := by gcongr
        _ = 1 := inv_mul_cancel₀ hl0.ne'
        _ ≤ 3 / 2 := by norm_num
    rw [setLIntegral_congr_fun (((measurable_const_smul _).comp hΦ) hs) this, lintegral_zero]
  · rw [ftMeasure_scaleM_muQ hφ hψ y₀ hq0.le lam x]
    exact (hC _).trans (decay_scale hc hC0 hlam1 x)

end TaoBR.Tao49.PartN
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
alias exists_scale_decayMeasure := TaoBR.Tao49.PartN.exists_scale_decayMeasure

alias conclusion_of_restrMu := TaoBR.Tao49.PartN.conclusion_of_restrMu

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartV
/-!
# Part V of the Theorem 4.9 Blueprint: degenerate cases and exponents
-/
/-! ## Easy lemmas -/
theorem conclusion_of_vanish {n m : ℕ} (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ) (y₀ : E m)
    (h : ∀ x, ψ x y₀ = 0) (q : ℝ≥0∞) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(E m, ℂ),
      eLpNorm (linearizedRestriction φ ψ y₀ f) q volume ≤ C * eLpNorm f q volume := by
  refine ⟨0, fun f => ?_⟩
  have : linearizedRestriction φ ψ y₀ f = 0 := by
    ext x; simp [linearizedRestriction, h x]
  rw [this, eLpNorm_zero]
  exact zero_le

end TaoBR.Tao49.PartV
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
/-! ## Degenerate cases -/
alias conclusion_of_vanish := TaoBR.Tao49.PartV.conclusion_of_vanish

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartV
theorem vol_zero_dim : (volume : Measure (E 0)) Set.univ = 1 := by
  have h := (PiLp.volume_preserving_ofLp (ι := Fin 0)).measure_preimage
    (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  simp only [Set.preimage_univ] at h
  rw [h, volume_pi, Measure.pi_univ]; simp

theorem integral_zero_dim (f : E 0 → ℂ) : ∫ x, f x = f 0 := by
  have : IsProbabilityMeasure (volume : Measure (E 0)) := ⟨vol_zero_dim⟩
  rw [integral_eq_const (c := f 0)]
  exact Filter.Eventually.of_forall fun x => by rw [Subsingleton.eq_zero x]

theorem conclusion_dim_zero (φ : E 0 → E 0 → ℝ) (ψ : E 0 → E 0 → ℂ) (y₀ : E 0) (q : ℝ≥0∞)
    (hq : 1 ≤ q) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(E 0, ℂ),
      eLpNorm (linearizedRestriction φ ψ y₀ f) q volume ≤ C * eLpNorm f q volume := by
  refine ⟨‖ψ 0 y₀‖₊, fun f => ?_⟩
  have : linearizedRestriction φ ψ y₀ f = ψ 0 y₀ • (f : E 0 → ℂ) := by
    ext x
    simp only [Pi.smul_apply]
    rw [Subsingleton.eq_zero x]
    simp only [linearizedRestriction, Real.fourier_eq, smul_eq_mul]
    rw [integral_zero_dim]
    simp
  rw [this, eLpNorm_const_smul]
  rfl

end TaoBR.Tao49.PartV
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
alias conclusion_dim_zero := TaoBR.Tao49.PartV.conclusion_dim_zero

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartV
theorem exists_exponent {p q : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hq : 1 ≤ q) (hqp : q < p) :
    ∃ r : ℝ, 1 < r ∧ q < r ∧ r < 2 ∧ r < 1 + q * (1 - 1 / p) := by
  have hp0 : 0 < p := by linarith
  have key : q < 1 + q * (1 - 1 / p) := by
    have : q * (1 / p) < 1 := by
      rw [mul_one_div, div_lt_one hp0]; exact hqp
    nlinarith
  set s := min 2 (1 + q * (1 - 1 / p)) with hs
  have hqs : q < s := lt_min (by linarith) key
  refine ⟨(q + s) / 2, by linarith, by linarith, ?_, ?_⟩
  · have := min_le_left 2 (1 + q * (1 - 1 / p)); linarith
  · have := min_le_right 2 (1 + q * (1 - 1 / p)); linarith

end TaoBR.Tao49.PartV
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
/-! ## Exponents -/
alias exists_exponent := TaoBR.Tao49.PartV.exists_exponent

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartV
theorem exists_small_alpha {q r : ℝ} (hq : 1 ≤ q) (hqr : q < r) (κ α₀ : ℝ) (hα₀ : 0 < α₀) :
    ∃ α : ℝ, 0 < α ∧ α < α₀ ∧ 1 / r + κ / Real.log (1 / α) < 1 / q := by
  have hq0 : 0 < q := by linarith
  set δ := 1 / q - 1 / r with hδ
  have hδ0 : 0 < δ := by
    rw [hδ, sub_pos]; exact one_div_lt_one_div_of_lt hq0 hqr
  set K := |κ| / δ + 1 with hK
  have hK0 : 0 < K := by positivity
  set α := min (α₀ / 2) (Real.exp (-K)) with hα
  have hαpos : 0 < α := lt_min (by linarith) (Real.exp_pos _)
  refine ⟨α, hαpos, lt_of_le_of_lt (min_le_left _ _) (by linarith), ?_⟩
  have hlog : K ≤ Real.log (1 / α) := by
    rw [one_div, Real.log_inv, le_neg, ← Real.exp_le_exp, Real.exp_log hαpos]
    exact min_le_right _ _
  have hlogpos : 0 < Real.log (1 / α) := hK0.trans_le hlog
  have h1 : κ / Real.log (1 / α) < δ := by
    rw [div_lt_iff₀ hlogpos]
    have h2 : |κ| < δ * K := by
      rw [hK, mul_add, mul_div_cancel₀ _ hδ0.ne', mul_one]; linarith
    have h3 : δ * K ≤ δ * Real.log (1 / α) := mul_le_mul_of_nonneg_left hlog hδ0.le
    linarith [le_abs_self κ]
  linarith

end TaoBR.Tao49.PartV
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartV
open Filter
open scoped Topology Real
/-! ## Modulated bumps -/
/-- The bump `χ`: `1` on `closedBall 0 (1/2)`, supported in `ball 0 1`. -/
noncomputable def chi (m : ℕ) : ContDiffBump (0 : E m) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- `h_L(y) = χ(y / L)`. -/
noncomputable def hb {m : ℕ} (L : ℝ) (y : E m) : ℂ := ((chi m (L⁻¹ • y) : ℝ) : ℂ)

/-- `g_{L,ζ}(y) = 𝐞(⟪y, ζ⟫) χ(y / L)`. -/
noncomputable def gt {m : ℕ} (L : ℝ) (ζ : E m) (y : E m) : ℂ := (𝐞 ⟪y, ζ⟫ : ℂ) * hb L y

theorem continuous_hb {m : ℕ} (L : ℝ) : Continuous (hb (m := m) L) :=
  Complex.continuous_ofReal.comp ((chi m).continuous.comp (continuous_const_smul _))

theorem continuous_gt {m : ℕ} (L : ℝ) (ζ : E m) : Continuous (gt L ζ) :=
  ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).subtype_val).mul
    (continuous_hb L)

theorem chi_eq_zero {m : ℕ} {v : E m} (hv : 1 ≤ ‖v‖) : chi m v = 0 := by
  have : v ∉ Function.support (chi m) := by
    rw [(chi m).support_eq]
    simp only [Metric.mem_ball, dist_zero_right, not_lt]
    exact hv
  exact Function.notMem_support.1 this

theorem norm_lt_of_chi_ne {m : ℕ} {L : ℝ} (hL : 0 < L) {y : E m} (hy : chi m (L⁻¹ • y) ≠ 0) :
    ‖y‖ < L := by
  by_contra h
  push Not at h
  apply hy
  apply chi_eq_zero
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hL.le), ← div_eq_inv_mul, le_div_iff₀ hL]
  linarith

theorem norm_hb_le {m : ℕ} (L : ℝ) (y : E m) : ‖hb L y‖ ≤ 1 := by
  rw [hb, Complex.norm_real, Real.norm_of_nonneg (chi m).nonneg]
  exact (chi m).le_one

theorem norm_gt_le {m : ℕ} (L : ℝ) (ζ y : E m) : ‖gt L ζ y‖ ≤ 1 := by
  rw [gt, norm_mul, Circle.norm_coe, one_mul]
  exact norm_hb_le L y

theorem gt_eq_zero {m : ℕ} {L : ℝ} (hL : 0 < L) (ζ : E m) {y : E m}
    (hy : y ∉ closedBall (0 : E m) L) : gt L ζ y = 0 := by
  have : chi m (L⁻¹ • y) = 0 := by
    by_contra h
    exact hy (by rw [mem_closedBall, dist_zero_right]; exact (norm_lt_of_chi_ne hL h).le)
  simp [gt, hb, this]

theorem integrable_hb {m : ℕ} (L : ℝ) (hL : 0 < L) : Integrable (hb (m := m) L) := by
  refine (continuous_hb L).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E m) L) fun y hy => ?_
  have : chi m (L⁻¹ • y) = 0 := by
    by_contra h
    exact hy (by rw [mem_closedBall, dist_zero_right]; exact (norm_lt_of_chi_ne hL h).le)
  simp [hb, this]

theorem fourier_gt {m : ℕ} (L : ℝ) (ζ ξ : E m) :
    𝓕 (gt L ζ) ξ = 𝓕 (hb L) (ξ - ζ) := by
  simp only [Real.fourier_eq]
  congr 1; ext y
  rw [gt, Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Circle.coe_mul,
    ← AddChar.map_add_eq_mul, inner_sub_right]
  congr 3
  ring

theorem continuous_fourier_hb {m : ℕ} (L : ℝ) (hL : 0 < L) : Continuous (𝓕 (hb (m := m) L)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simpa using (continuous_inner : Continuous fun p : E m × E m => ⟪p.1, p.2⟫))
    (integrable_hb L hL)

theorem cos_ge_half {x : ℝ} (hx : |x| ≤ 1 / 2) : 1 / 2 ≤ Real.cos x := by
  have h := Real.cos_bound (hx.trans (by norm_num))
  have h1 := (abs_sub_le_iff.1 h).2
  have hx2 : x ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg x]
  have hx4 : |x| ^ 4 ≤ 1 / 16 := by
    have : |x| ^ 4 = (x ^ 2) ^ 2 := by rw [← sq_abs x]; ring
    rw [this]; nlinarith [sq_nonneg x]
  nlinarith

/-- The key lower bound: `|ĥ_L(v)| ≥ L^m (∫ χ) / 2` for `|v| ≤ 1/(16 L)`. -/
theorem fourier_hb_lower {m : ℕ} {L : ℝ} (hL : 0 < L) {v : E m} (hv : ‖v‖ ≤ 1 / (16 * L)) :
    L ^ m * (∫ w, chi m w) / 2 ≤ ‖𝓕 (hb (m := m) L) v‖ := by
  have hint : Integrable fun y : E m => 𝐞 (-⟪y, v⟫) • hb L y := by
    refine (integrable_hb L hL).norm.mono' ?_ (ae_of_all _ fun y => ?_)
    · exact ((Real.continuous_fourierChar.comp
        (continuous_id.inner continuous_const).neg).smul (continuous_hb L)).aestronglyMeasurable
    · rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
  rw [Real.fourier_eq]
  refine le_trans ?_ ((integral_re hint).trans_le (Complex.re_le_norm _))
  have hpt : ∀ y : E m, (1 / 2 : ℝ) * chi m (L⁻¹ • y) ≤ RCLike.re (𝐞 (-⟪y, v⟫) • hb L y) := by
    intro y
    have hre : RCLike.re (𝐞 (-⟪y, v⟫) • hb L y) = Real.cos (2 * π * ⟪y, v⟫) * chi m (L⁻¹ • y) := by
      rw [Circle.smul_def, smul_eq_mul, hb, Real.fourierChar_apply]
      change (Complex.exp _ * _).re = _
      rw [Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, ← Real.cos_neg]
      congr 2; ring
    rw [hre]
    by_cases hc : chi m (L⁻¹ • y) = 0
    · rw [hc]; simp
    · have hy := norm_lt_of_chi_ne hL hc
      have h1 : |⟪y, v⟫| ≤ 1 / 16 := by
        refine (abs_real_inner_le_norm y v).trans ?_
        calc ‖y‖ * ‖v‖ ≤ L * (1 / (16 * L)) := by gcongr
          _ = 1 / 16 := by field_simp
      have h2 : |2 * π * ⟪y, v⟫| ≤ 1 / 2 := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
        have := Real.pi_lt_d2
        nlinarith [abs_nonneg ⟪y, v⟫]
      have := cos_ge_half h2
      have := (chi m).nonneg (x := L⁻¹ • y)
      nlinarith
  have hI : ∫ y : E m, (1 / 2 : ℝ) * chi m (L⁻¹ • y) = L ^ m * (∫ w, chi m w) / 2 := by
    rw [integral_const_mul]
    have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (E m))
      (fun w => chi m w) hL.le
    rw [finrank_euclideanSpace_fin, smul_eq_mul] at h
    rw [h]; ring
  rw [← hI]
  refine integral_mono ?_ hint.re hpt
  exact ((integrable_hb L hL).norm.const_mul (1 / 2)).congr (ae_of_all _ fun y => by
    simp [hb, Real.norm_of_nonneg (chi m).nonneg])

/-! ## Generic tools -/
theorem continuous_Grad' {n m : ℕ} {φ : E n → E m → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ)) (y₀ : E m) :
    Continuous fun x => gradient (fun y => φ x y) y₀ := by
  have h : ContDiff ℝ 0 (fun x => fderiv ℝ (fun y => φ x y) ((fun _ : E n => y₀) x)) :=
    ContDiff.fderiv (f := φ) hφ contDiff_const (by norm_cast)
  exact (InnerProductSpace.toDual ℝ (E m)).symm.continuous.comp h.continuous

theorem continuous_psi {n m : ℕ} {ψ : E n → E m → ℂ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (y₀ : E m) : Continuous fun x => ψ x y₀ :=
  hψ.continuous.comp (continuous_id.prodMk continuous_const)

theorem lr_gt {n m : ℕ} (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ) (y₀ : E m) (L : ℝ) (ζ : E m)
    (x : E n) :
    linearizedRestriction φ ψ y₀ (gt L ζ) x =
      ψ x y₀ * 𝓕 (hb L) (gradient (fun y => φ x y) y₀ - ζ) := by
  rw [linearizedRestriction, fourier_gt]

theorem continuous_lr_gt {n m : ℕ} {φ : E n → E m → ℝ} {ψ : E n → E m → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (y₀ : E m) {L : ℝ} (hL : 0 < L) (ζ : E m) :
    Continuous (linearizedRestriction φ ψ y₀ (gt L ζ)) := by
  have : linearizedRestriction φ ψ y₀ (gt L ζ) =
      fun x => ψ x y₀ * 𝓕 (hb L) (gradient (fun y => φ x y) y₀ - ζ) := by
    ext x; exact lr_gt φ ψ y₀ L ζ x
  rw [this]
  exact (continuous_psi hψ y₀).mul
    ((continuous_fourier_hb L hL).comp ((continuous_Grad' hφ y₀).sub continuous_const))

/-- Apply the localized estimate to `g_{L,ζ}`. -/
theorem hL_gt {n m : ℕ} {φ : E n → E m → ℝ} {ψ : E n → E m → ℂ} {y₀ : E m} {p : ℝ≥0∞}
    {ε C : ℝ}
    (hC : ∀ L : ℝ, 1 ≤ L → ∀ g : E m → ℂ, Measurable g →
      (∃ B : ℝ, ∀ y, ‖g y‖ ≤ B) → (∀ y, y ∉ closedBall (0 : E m) L → g y = 0) →
        eLpNorm (linearizedRestriction φ ψ y₀ g) p volume ≤
          ENNReal.ofReal (C * L ^ ε) * eLpNorm g p volume)
    {L : ℝ} (hL : 1 ≤ L) (ζ : E m) :
    eLpNorm (linearizedRestriction φ ψ y₀ (gt L ζ)) p volume ≤
      ENNReal.ofReal (C * L ^ ε) * eLpNorm (gt L ζ) p volume :=
  hC L hL _ (continuous_gt L ζ).measurable ⟨1, norm_gt_le L ζ⟩
    (fun _ hy => gt_eq_zero (by linarith) ζ hy)

theorem enorm_le_eLpNorm_top {k : ℕ} {F : E k → ℂ} (hF : Continuous F) (x : E k) :
    ‖F x‖ₑ ≤ eLpNorm F ⊤ volume := by
  rw [eLpNorm_exponent_top]
  by_contra h
  push Not at h
  have hU : IsOpen {y | eLpNormEssSup F volume < ‖F y‖ₑ} :=
    isOpen_lt continuous_const hF.enorm
  have h0 : volume {y | eLpNormEssSup F volume < ‖F y‖ₑ} = 0 := by
    have := ae_le_eLpNormEssSup (f := F) (μ := volume)
    rw [ae_iff] at this
    simpa only [not_le] using this
  have hne : ({y | eLpNormEssSup F volume < ‖F y‖ₑ} : Set (E k)).Nonempty := ⟨x, h⟩
  exact (hU.measure_pos volume hne).ne' h0

theorem eLpNorm_gt_top_le {m : ℕ} (L : ℝ) (ζ : E m) : eLpNorm (gt L ζ) ⊤ volume ≤ 1 := by
  refine (eLpNorm_le_of_ae_bound (C := 1) (ae_of_all _ fun y => norm_gt_le L ζ y)).trans ?_
  simp

theorem le_zero_of_forall_le_rpow {c K s : ℝ} (hs : 0 < s)
    (h : ∀ L : ℝ, 1 ≤ L → c ≤ K * L ^ (-s)) : c ≤ 0 := by
  have ht : Tendsto (fun L : ℝ => K * L ^ (-s)) atTop (𝓝 (K * 0)) :=
    (tendsto_rpow_neg_atTop hs).const_mul K
  rw [mul_zero] at ht
  exact ge_of_tendsto ht ((eventually_ge_atTop 1).mono h)

theorem chi_integral_pos (m : ℕ) : 0 < ∫ w, chi m w := (chi m).integral_pos

/-! ## `vanish_of_top` -/
theorem vanish_of_top {n m : ℕ} (hm : 1 ≤ m) (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (y₀ : E m)
    (hL : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ L : ℝ, 1 ≤ L → ∀ g : E m → ℂ, Measurable g →
      (∃ B : ℝ, ∀ y, ‖g y‖ ≤ B) → (∀ y, y ∉ closedBall (0 : E m) L → g y = 0) →
        eLpNorm (linearizedRestriction φ ψ y₀ g) ⊤ volume ≤
          ENNReal.ofReal (C * L ^ ε) * eLpNorm g ⊤ volume) :
    ∀ x, ψ x y₀ = 0 := by
  intro x
  by_contra hx
  have ha : 0 < ‖ψ x y₀‖ := norm_pos_iff.2 hx
  set a := ‖ψ x y₀‖
  set I := ∫ w, chi m w
  have hI := chi_integral_pos m
  obtain ⟨C, hC⟩ := hL (1 / 2) (by norm_num)
  have key : ∀ L : ℝ, 1 ≤ L → a * I / 2 ≤ C * L ^ (-(1 / 2 : ℝ)) := by
    intro L hL1
    have hL0 : 0 < L := by linarith
    set ζ := gradient (fun y => φ x y) y₀
    have h1 := hL_gt hC hL1 ζ
    have h2 := enorm_le_eLpNorm_top (continuous_lr_gt hφ hψ y₀ hL0 ζ) x
    have h3 : eLpNorm (linearizedRestriction φ ψ y₀ (gt L ζ)) ⊤ volume ≤
        ENNReal.ofReal (C * L ^ (1 / 2 : ℝ)) :=
      h1.trans (by
        calc _ ≤ ENNReal.ofReal (C * L ^ (1 / 2 : ℝ)) * 1 := by
              gcongr; exact eLpNorm_gt_top_le L ζ
          _ = _ := mul_one _)
    have h4 : a * (L ^ m * I / 2) ≤ ‖linearizedRestriction φ ψ y₀ (gt L ζ) x‖ := by
      rw [lr_gt, norm_mul, sub_self]
      gcongr
      exact fourier_hb_lower hL0 (by rw [norm_zero]; positivity)
    have hpos : 0 < a * (L ^ m * I / 2) := by positivity
    have h5 : ENNReal.ofReal (a * (L ^ m * I / 2)) ≤ ENNReal.ofReal (C * L ^ (1 / 2 : ℝ)) := by
      refine le_trans ?_ (h2.trans h3)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal h4
    have h6 : a * (L ^ m * I / 2) ≤ C * L ^ (1 / 2 : ℝ) := by
      rcases (ENNReal.ofReal_le_ofReal_iff').1 h5 with h | h
      · exact h
      · linarith
    -- `L^m ≥ L = L^{1/2} L^{1/2}`
    set t := L ^ (1 / 2 : ℝ) with ht
    have ht0 : 0 < t := Real.rpow_pos_of_pos hL0 _
    have htt : t * t = L := by
      rw [ht, ← Real.rpow_add hL0]; norm_num
    have hLm : L ≤ L ^ m := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ m := pow_le_pow_right₀ hL1 hm
    have h7 : a * I / 2 * (t * t) ≤ C * t := by
      calc a * I / 2 * (t * t) ≤ a * I / 2 * L ^ m := by
            rw [htt]; gcongr
        _ = a * (L ^ m * I / 2) := by ring
        _ ≤ C * t := h6
    have h8 : a * I / 2 * t ≤ C := by
      have := (mul_le_mul_iff_of_pos_right ht0).1 (by nlinarith : a * I / 2 * t * t ≤ C * t)
      exact this
    rw [Real.rpow_neg hL0.le, ← ht, ← div_eq_mul_inv, le_div_iff₀ ht0]
    exact h8
  have := le_zero_of_forall_le_rpow (by norm_num : (0 : ℝ) < 1 / 2) key
  have : 0 < a * I / 2 := by positivity
  linarith

end TaoBR.Tao49.PartV
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
alias vanish_of_top := TaoBR.Tao49.PartV.vanish_of_top

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49.PartV
open Filter
open scoped Topology Real
/-! ## Tools for real exponents -/
theorem lint_le_of_eLpNorm_le {k k' : ℕ} {F : E k → ℂ} {G : E k' → ℂ} {p : ℝ} (hp : 0 < p)
    {K : ℝ≥0∞}
    (h : eLpNorm F (ENNReal.ofReal p) volume ≤ K * eLpNorm G (ENNReal.ofReal p) volume) :
    ∫⁻ x, ‖F x‖ₑ ^ p ≤ K ^ p * ∫⁻ y, ‖G y‖ₑ ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le] at h
  have := ENNReal.rpow_le_rpow h hp.le
  rwa [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    one_div_mul_cancel hp.ne', ENNReal.rpow_one, ENNReal.rpow_one] at this

theorem lint_gt_le {m : ℕ} {L : ℝ} (hL : 0 < L) (ζ : E m) {p : ℝ} (hp : 0 < p) :
    ∫⁻ y, ‖gt L ζ y‖ₑ ^ p ≤ volume (closedBall (0 : E m) L) := by
  rw [← lintegral_indicator_one measurableSet_closedBall]
  refine lintegral_mono fun y => ?_
  by_cases hy : y ∈ closedBall (0 : E m) L
  · rw [indicator_of_mem hy, Pi.one_apply]
    refine ENNReal.rpow_le_one ?_ hp.le
    rw [← ofReal_norm, ENNReal.ofReal_le_one]
    exact norm_gt_le L ζ y
  · rw [indicator_of_notMem hy, gt_eq_zero hL ζ hy, enorm_zero, ENNReal.zero_rpow_of_pos hp]

/-- The localized estimate, raised to the power `p`, on `g_{L,ζ}`. -/
theorem lint_lr_le {n m : ℕ} {φ : E n → E m → ℝ} {ψ : E n → E m → ℂ} {y₀ : E m} {p : ℝ}
    (hp : 0 < p) {ε C : ℝ}
    (hC : ∀ L : ℝ, 1 ≤ L → ∀ g : E m → ℂ, Measurable g →
      (∃ B : ℝ, ∀ y, ‖g y‖ ≤ B) → (∀ y, y ∉ closedBall (0 : E m) L → g y = 0) →
        eLpNorm (linearizedRestriction φ ψ y₀ g) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * L ^ ε) * eLpNorm g (ENNReal.ofReal p) volume)
    {L : ℝ} (hL : 1 ≤ L) (ζ : E m) :
    ∫⁻ x, ‖linearizedRestriction φ ψ y₀ (gt L ζ) x‖ₑ ^ p ≤
      ENNReal.ofReal (max C 0 * L ^ ε) ^ p * volume (closedBall (0 : E m) L) := by
  refine (lint_le_of_eLpNorm_le hp (hL_gt hC hL ζ)).trans ?_
  gcongr
  · exact le_max_left _ _
  · exact lint_gt_le (by linarith) ζ hp

theorem le_zero_of_forall_le_rpow' {c K s e : ℝ} (hs : 0 < s)
    (h : ∀ L : ℝ, 1 ≤ L → c * L ^ (s + e) ≤ K * L ^ e) : c ≤ 0 := by
  refine le_zero_of_forall_le_rpow (K := K) hs fun L hL => ?_
  have hL0 : 0 < L := by linarith
  have he : 0 < L ^ e := Real.rpow_pos_of_pos hL0 e
  have h1 := h L hL
  rw [Real.rpow_add hL0, ← mul_assoc] at h1
  have h2 : c * L ^ s ≤ K := (mul_le_mul_iff_of_pos_right he).1 h1
  rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hL0 s)]
  exact h2

theorem vol_closedBall {k : ℕ} (x : E k) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x r) =
      ENNReal.ofReal (r ^ k * (volume (closedBall (0 : E k) 1)).toReal) := by
  rw [Measure.addHaar_closedBall' _ x hr, finrank_euclideanSpace_fin,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal measure_closedBall_lt_top.ne]

/-! ## `vanish_of_rank_zero` -/
theorem fderiv_y_contDiff {n m : ℕ} {φ : E n → E m → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ)) (y₀ : E m) :
    ContDiff ℝ 1 fun x => fderiv ℝ (fun y => φ x y) y₀ :=
  ContDiff.fderiv (f := φ) (g := fun _ : E n => y₀) hφ contDiff_const (by norm_cast)

theorem mixedHessian_eq_zero {n m : ℕ} {φ : E n → E m → ℝ} {ψ : E n → E m → ℂ}
    (hrank : HasConstantRank φ ψ 0) {x : E n} {y₀ : E m} (hx : ψ x y₀ ≠ 0) :
    mixedHessian φ x y₀ = 0 := by
  have h := hrank x y₀ (subset_tsupport _ hx)
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext v
  exact LinearMap.congr_fun h v ▸ rfl

theorem grad_const_on_ball {n m : ℕ} {φ : E n → E m → ℝ} {ψ : E n → E m → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ)) (hrank : HasConstantRank φ ψ 0) (y₀ : E m)
    {x₁ : E n} {δ : ℝ} (hB : ∀ x ∈ ball x₁ δ, ψ x y₀ ≠ 0) (hδ : 0 < δ) :
    ∀ x ∈ ball x₁ δ, gradient (fun y => φ x y) y₀ = gradient (fun y => φ x₁ y) y₀ := by
  intro x hx
  have hd := (fderiv_y_contDiff hφ y₀).differentiable one_ne_zero
  have hconst := (convex_ball x₁ δ).is_const_of_fderivWithin_eq_zero hd.differentiableOn
    (fun z hz => by
      rw [fderivWithin_of_isOpen isOpen_ball hz]
      exact mixedHessian_eq_zero hrank (hB z hz)) hx (mem_ball_self hδ)
  simp only [gradient, hconst]

theorem vanish_of_rank_zero {n : ℕ} (φ : E n → E 1 → ℝ) (ψ : E n → E 1 → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (hrank : HasConstantRank φ ψ 0) (y₀ : E 1) {p : ℝ} (hp : 1 < p)
    (hL : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ L : ℝ, 1 ≤ L → ∀ g : E 1 → ℂ, Measurable g →
      (∃ B : ℝ, ∀ y, ‖g y‖ ≤ B) → (∀ y, y ∉ closedBall (0 : E 1) L → g y = 0) →
        eLpNorm (linearizedRestriction φ ψ y₀ g) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * L ^ ε) * eLpNorm g (ENNReal.ofReal p) volume) :
    ∀ x, ψ x y₀ = 0 := by
  intro x₁
  by_contra hx
  have hp0 : 0 < p := by linarith
  have ha : 0 < ‖ψ x₁ y₀‖ := norm_pos_iff.2 hx
  set a := ‖ψ x₁ y₀‖
  set I := ∫ w, chi 1 w
  have hI := chi_integral_pos 1
  -- a ball where `|ψ(·, y₀)| > a/2`
  have hev : ∀ᶠ x in 𝓝 x₁, a / 2 < ‖ψ x y₀‖ :=
    continuousAt_const.eventually_lt (continuous_psi hψ y₀).norm.continuousAt
      (by show a / 2 < a; linarith)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hB : ∀ x ∈ ball x₁ δ, ψ x y₀ ≠ 0 := fun x hx h => by
    have := hball x hx; rw [h, norm_zero] at this; linarith
  have hconst := grad_const_on_ball hφ hrank y₀ hB hδ
  set ζ := gradient (fun y => φ x₁ y) y₀
  set ε := (p - 1) / (2 * p) with hε
  obtain ⟨C, hC⟩ := hL ε (by rw [hε]; apply div_pos <;> linarith)
  set C' := max C 0
  set vB := (volume (ball x₁ δ)).toReal
  have hvB : 0 < vB := ENNReal.toReal_pos (measure_ball_pos volume x₁ hδ).ne'
    measure_ball_lt_top.ne
  set v1 := (volume (closedBall (0 : E 1) 1)).toReal
  have key : ∀ L : ℝ, 1 ≤ L →
      vB * (a / 2 * (I / 2)) ^ p * L ^ ((p - 1) / 2 + (ε * p + 1)) ≤
        C' ^ p * v1 * L ^ (ε * p + 1) := by
    intro L hL1
    have hL0 : 0 < L := by linarith
    set X := a / 2 * (L ^ 1 * I / 2)
    have hX : 0 ≤ X := by positivity
    have hlow : ∀ x ∈ ball x₁ δ, ENNReal.ofReal X ^ p ≤
        ‖linearizedRestriction φ ψ y₀ (gt L ζ) x‖ₑ ^ p := by
      intro x hx
      gcongr
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      rw [lr_gt, norm_mul, hconst x hx, sub_self]
      exact mul_le_mul (hball x hx).le (fourier_hb_lower hL0 (by rw [norm_zero]; positivity))
        (by positivity) (norm_nonneg _)
    have hmeas : Measurable fun x => ‖linearizedRestriction φ ψ y₀ (gt L ζ) x‖ₑ ^ p :=
      (continuous_lr_gt hφ hψ y₀ hL0 ζ).measurable.enorm.pow_const p
    have h1 : ENNReal.ofReal X ^ p * volume (ball x₁ δ) ≤
        ENNReal.ofReal (C' * L ^ ε) ^ p * volume (closedBall (0 : E 1) L) := by
      calc ENNReal.ofReal X ^ p * volume (ball x₁ δ)
          = ∫⁻ x in ball x₁ δ, ENNReal.ofReal X ^ p := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ x in ball x₁ δ, ‖linearizedRestriction φ ψ y₀ (gt L ζ) x‖ₑ ^ p :=
            setLIntegral_mono hmeas hlow
        _ ≤ ∫⁻ x, ‖linearizedRestriction φ ψ y₀ (gt L ζ) x‖ₑ ^ p := setLIntegral_le_lintegral _ _
        _ ≤ _ := lint_lr_le hp0 hC hL1 ζ
    rw [vol_closedBall _ hL0.le, ← ENNReal.ofReal_toReal (measure_ball_lt_top (x := x₁)
      (r := δ)).ne, ENNReal.ofReal_rpow_of_nonneg hX hp0.le,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    -- real algebra
    have e1 : X ^ p = (a / 2 * (I / 2)) ^ p * L ^ p := by
      rw [← Real.mul_rpow (by positivity) hL0.le]; congr 1; ring
    have e2 : (C' * L ^ ε) ^ p = C' ^ p * L ^ (ε * p) := by
      rw [Real.mul_rpow (le_max_right _ _) (by positivity), ← Real.rpow_mul hL0.le]
    have e3 : (p - 1) / 2 + (ε * p + 1) = p := by
      rw [hε]; field_simp; ring
    have e4 : L ^ (ε * p + 1) = L ^ (ε * p) * L ^ (1 : ℕ) := by
      rw [Real.rpow_add hL0, Real.rpow_one, pow_one]
    rw [e3, e4]
    rw [e1, e2] at h1
    linarith [h1]
  have := le_zero_of_forall_le_rpow' (by linarith : (0 : ℝ) < (p - 1) / 2) key
  have : 0 < vB * (a / 2 * (I / 2)) ^ p := by positivity
  linarith

/-! ## `vanish_of_gt_two` -/
theorem psi_slice_support {n m : ℕ} {ψ : E n → E m → ℂ}
    (hψc : HasCompactSupport (Function.uncurry ψ)) (y₀ : E m) :
    ∃ K : Set (E n), IsCompact K ∧ ∀ x, ψ x y₀ ≠ 0 → x ∈ K := by
  refine ⟨Prod.fst '' tsupport (Function.uncurry ψ), hψc.image continuous_fst, fun x hx => ?_⟩
  exact ⟨(x, y₀), subset_tsupport _ hx, rfl⟩

theorem lintegral_dens_ne_top {n m : ℕ} {ψ : E n → E m → ℂ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (y₀ : E m) {q : ℝ} (hq : 0 < q) :
    ∫⁻ x, ‖ψ x y₀‖ₑ ^ q ≠ ⊤ := by
  obtain ⟨K, hK, hKs⟩ := psi_slice_support hψc y₀
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuous_psi hψ y₀).continuousOn
  have hle : ∀ x, ‖ψ x y₀‖ₑ ^ q ≤ K.indicator (fun _ => ENNReal.ofReal B ^ q) x := by
    intro x
    by_cases hx : ψ x y₀ = 0
    · rw [hx, enorm_zero, ENNReal.zero_rpow_of_pos hq]; exact zero_le
    · rw [indicator_of_mem (hKs x hx)]
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB x (hKs x hx))
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_indicator_const hK.measurableSet]
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
    hK.measure_lt_top.ne

/-- The averaged inequality: `A W ≤ R |B_ζ|`, `A = ∫ |ψ(·, y₀)|^p`. -/
theorem averaged_bound {n m : ℕ} {φ : E n → E m → ℝ} {ψ : E n → E m → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (y₀ : E m) {p : ℝ} (hp : 0 < p)
    {M : ℝ} (hM : ∀ x, ψ x y₀ ≠ 0 → ‖gradient (fun y => φ x y) y₀‖ ≤ M)
    {ε C : ℝ}
    (hC : ∀ L : ℝ, 1 ≤ L → ∀ g : E m → ℂ, Measurable g →
      (∃ B : ℝ, ∀ y, ‖g y‖ ≤ B) → (∀ y, y ∉ closedBall (0 : E m) L → g y = 0) →
        eLpNorm (linearizedRestriction φ ψ y₀ g) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * L ^ ε) * eLpNorm g (ENNReal.ofReal p) volume)
    {L : ℝ} (hL : 1 ≤ L) :
    (∫⁻ x, ‖ψ x y₀‖ₑ ^ p) * (volume (closedBall (0 : E m) (1 / (16 * L))) *
        ENNReal.ofReal (L ^ m * (∫ w, chi m w) / 2) ^ p) ≤
      ENNReal.ofReal (max C 0 * L ^ ε) ^ p * volume (closedBall (0 : E m) L) *
        volume (closedBall (0 : E m) (M + 1)) := by
  have hL0 : 0 < L := by linarith
  set Fh := 𝓕 (hb (m := m) L)
  have hcF : Continuous Fh := continuous_fourier_hb L hL0
  have hΦ := continuous_Grad' hφ y₀
  set f2 : E m → E n → ℝ≥0∞ := fun ζ x =>
    ‖ψ x y₀‖ₑ ^ p * ‖Fh (gradient (fun y => φ x y) y₀ - ζ)‖ₑ ^ p with hf2
  have hf2m : Measurable (Function.uncurry f2) := by
    refine Measurable.mul ?_ ?_
    · exact ((continuous_psi hψ y₀).comp continuous_snd).measurable.enorm.pow_const p
    · exact (hcF.comp ((hΦ.comp continuous_snd).sub continuous_fst)).measurable.enorm.pow_const p
  set R := ENNReal.ofReal (max C 0 * L ^ ε) ^ p * volume (closedBall (0 : E m) L)
  have hup : ∀ ζ, ∫⁻ x, f2 ζ x ≤ R := by
    intro ζ
    refine le_trans (le_of_eq ?_) (lint_lr_le hp hC hL ζ)
    refine lintegral_congr fun x => ?_
    rw [lr_gt, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  set r := 1 / (16 * L)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  set W := volume (closedBall (0 : E m) r) * ENNReal.ofReal (L ^ m * (∫ w, chi m w) / 2) ^ p
  have hlow : ∀ x, ‖ψ x y₀‖ₑ ^ p * W ≤ ∫⁻ ζ in closedBall (0 : E m) (M + 1), f2 ζ x := by
    intro x
    by_cases hx : ψ x y₀ = 0
    · rw [hx, enorm_zero, ENNReal.zero_rpow_of_pos hp, zero_mul]; exact zero_le
    have hmeasζ : Measurable fun ζ => ‖Fh (gradient (fun y => φ x y) y₀ - ζ)‖ₑ ^ p :=
      (hcF.comp (continuous_const.sub continuous_id)).measurable.enorm.pow_const p
    simp only [hf2]
    rw [lintegral_const_mul _ hmeasζ]
    gcongr
    set ξ := gradient (fun y => φ x y) y₀
    have hsub : closedBall ξ r ⊆ closedBall (0 : E m) (M + 1) := by
      intro ζ hζ
      rw [mem_closedBall, dist_zero_right]
      rw [mem_closedBall, dist_eq_norm] at hζ
      have := hM x hx
      calc ‖ζ‖ = ‖ξ - (ξ - ζ)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖ξ‖ + ‖ξ - ζ‖ := norm_sub_le _ _
        _ ≤ M + 1 := by rw [norm_sub_rev]; linarith
    calc W = ∫⁻ ζ in closedBall ξ r, ENNReal.ofReal (L ^ m * (∫ w, chi m w) / 2) ^ p := by
          simp only [W]
          rw [setLIntegral_const, mul_comm, vol_closedBall (0 : E m) hr0, vol_closedBall ξ hr0]
      _ ≤ ∫⁻ ζ in closedBall ξ r, ‖Fh (ξ - ζ)‖ₑ ^ p := by
          refine setLIntegral_mono hmeasζ fun ζ hζ => ?_
          gcongr
          rw [← ofReal_norm]
          apply ENNReal.ofReal_le_ofReal
          refine fourier_hb_lower hL0 ?_
          rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at hζ
          exact hζ
      _ ≤ _ := lintegral_mono_set hsub
  calc (∫⁻ x, ‖ψ x y₀‖ₑ ^ p) * W = ∫⁻ x, ‖ψ x y₀‖ₑ ^ p * W :=
        (lintegral_mul_const _ ((continuous_psi hψ y₀).measurable.enorm.pow_const p)).symm
    _ ≤ ∫⁻ x, ∫⁻ ζ in closedBall (0 : E m) (M + 1), f2 ζ x := lintegral_mono hlow
    _ = ∫⁻ ζ in closedBall (0 : E m) (M + 1), ∫⁻ x, f2 ζ x :=
        (lintegral_lintegral_swap hf2m.aemeasurable).symm
    _ ≤ ∫⁻ ζ in closedBall (0 : E m) (M + 1), R := setLIntegral_mono measurable_const
        fun ζ _ => hup ζ
    _ = R * volume (closedBall (0 : E m) (M + 1)) := setLIntegral_const _ _

theorem vanish_of_gt_two {n m : ℕ} (hm : 1 ≤ m) (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (y₀ : E m) {p : ℝ} (hp : 2 < p)
    (hL : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ L : ℝ, 1 ≤ L → ∀ g : E m → ℂ, Measurable g →
      (∃ B : ℝ, ∀ y, ‖g y‖ ≤ B) → (∀ y, y ∉ closedBall (0 : E m) L → g y = 0) →
        eLpNorm (linearizedRestriction φ ψ y₀ g) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * L ^ ε) * eLpNorm g (ENNReal.ofReal p) volume) :
    ∀ x, ψ x y₀ = 0 := by
  have hp0 : 0 < p := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨K, hK, hKs⟩ := psi_slice_support hψc y₀
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (continuous_Grad' hφ y₀).continuousOn
  set M := max M₀ 0
  have hM : ∀ x, ψ x y₀ ≠ 0 → ‖gradient (fun y => φ x y) y₀‖ ≤ M := fun x hx =>
    (hM₀ x (hKs x hx)).trans (le_max_left _ _)
  set A := ∫⁻ x, ‖ψ x y₀‖ₑ ^ p
  have hA : A ≠ ⊤ := lintegral_dens_ne_top hψ hψc y₀ hp0
  set I := ∫ w, chi m w
  have hI := chi_integral_pos m
  set ε := (m : ℝ) * (p - 2) / (2 * p) with hε
  obtain ⟨C, hC⟩ := hL ε (by rw [hε]; apply div_pos <;> nlinarith)
  set C' := max C 0
  set v1 := (volume (closedBall (0 : E m) 1)).toReal
  have hv1 : 0 < v1 := ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne'
    measure_closedBall_lt_top.ne
  set vbz := (volume (closedBall (0 : E m) (M + 1))).toReal
  set s := (m : ℝ) * (p - 2) / 2
  have hs : 0 < s := by positivity
  set e := ε * p + m
  have key : ∀ L : ℝ, 1 ≤ L →
      (A.toReal * (I / 2) ^ p / 16 ^ m * v1) * L ^ (s + e) ≤ (vbz * C' ^ p * v1) * L ^ e := by
    intro L hL1
    have hL0 : 0 < L := by linarith
    have h1 : A * (volume (closedBall (0 : E m) (1 / (16 * L))) *
        ENNReal.ofReal (L ^ m * I / 2) ^ p) ≤ ENNReal.ofReal (C' * L ^ ε) ^ p *
          volume (closedBall (0 : E m) L) * volume (closedBall (0 : E m) (M + 1)) :=
      averaged_bound hφ hψ y₀ hp0 hM hC hL1
    have hX : 0 ≤ L ^ m * I / 2 := by positivity
    rw [← ENNReal.ofReal_toReal hA, vol_closedBall _ (by positivity), vol_closedBall _ hL0.le,
      ← ENNReal.ofReal_toReal (measure_closedBall_lt_top (x := (0 : E m)) (r := M + 1)).ne,
      ENNReal.ofReal_rpow_of_nonneg hX hp0.le,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    have e1 : (1 / (16 * L)) ^ m * v1 * (L ^ m * I / 2) ^ p =
        (I / 2) ^ p / 16 ^ m * v1 * L ^ (s + e) := by
      have hse : s + e = (m : ℝ) * p - m := by
        simp only [s, e, hε]; field_simp; ring
      rw [hse, Real.rpow_sub hL0, Real.rpow_natCast, Real.rpow_mul hL0.le, Real.rpow_natCast,
        show L ^ m * I / 2 = L ^ m * (I / 2) by ring, Real.mul_rpow (by positivity) (by positivity),
        div_pow, mul_pow]
      field_simp
      rw [one_pow, one_mul]
    have e2 : (C' * L ^ ε) ^ p * (L ^ m * v1) * vbz = vbz * C' ^ p * v1 * L ^ e := by
      rw [Real.mul_rpow (le_max_right _ _) (by positivity), ← Real.rpow_mul hL0.le,
        Real.rpow_add hL0, Real.rpow_natCast]
      ring
    calc (A.toReal * (I / 2) ^ p / 16 ^ m * v1) * L ^ (s + e)
        = A.toReal * ((I / 2) ^ p / 16 ^ m * v1 * L ^ (s + e)) := by ring
      _ = A.toReal * ((1 / (16 * L)) ^ m * v1 * (L ^ m * I / 2) ^ p) := by rw [e1]
      _ ≤ (C' * L ^ ε) ^ p * (L ^ m * v1) * vbz := h1
      _ = _ := e2
  have hc := le_zero_of_forall_le_rpow' hs key
  have hpos : 0 < (I / 2) ^ p / 16 ^ m * v1 := by positivity
  have hA0 : A.toReal = 0 := by
    have : A.toReal * ((I / 2) ^ p / 16 ^ m * v1) ≤ 0 := by
      calc A.toReal * ((I / 2) ^ p / 16 ^ m * v1) = A.toReal * (I / 2) ^ p / 16 ^ m * v1 := by
            ring
        _ ≤ 0 := hc
    exact le_antisymm (nonpos_of_mul_nonpos_left this hpos) ENNReal.toReal_nonneg
  have hA00 : A = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff A).1 hA0 with h | h
    · exact h
    · exact absurd h hA
  rw [lintegral_eq_zero_iff ((continuous_psi hψ y₀).measurable.enorm.pow_const p)] at hA00
  have hae : (fun x => ψ x y₀) =ᵐ[volume] fun _ => (0 : ℂ) := by
    filter_upwards [hA00] with x hx
    simp only [Pi.zero_apply] at hx
    rcases (ENNReal.rpow_eq_zero_iff).1 hx with h | h
    · exact enorm_eq_zero.1 h.1
    · linarith [h.2]
  have := ((continuous_psi hψ y₀).ae_eq_iff_eq volume continuous_const).1 hae
  exact fun x => congr_fun this x

end TaoBR.Tao49.PartV
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR.Tao49
alias vanish_of_gt_two := TaoBR.Tao49.PartV.vanish_of_gt_two

alias vanish_of_rank_zero := TaoBR.Tao49.PartV.vanish_of_rank_zero

alias exists_small_alpha := TaoBR.Tao49.PartV.exists_small_alpha

end TaoBR.Tao49
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
namespace TaoBR
open Tao49
/-- **Target** (Tao, Theorem 4.9, p. 10), proved from the stubs. -/
theorem linearizedRestriction_le_of_oscillatoryOp_le_dev (n m : ℕ) (hnm : m - 1 ≤ n) (hmn : n ≤ m)
    (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (hrank : HasConstantRank φ ψ (m - 1)) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hS : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      opNorm p p (oscillatoryOp φ ψ R) ≤
        ENNReal.ofReal (C * R ^ (-((m : ℝ) * (conjExp p)⁻¹.toReal) + ε))) :
    ∀ y₀ : E m, ∀ q : ℝ≥0∞, 1 ≤ q → q < p → ∃ C : ℝ≥0, ∀ f : 𝓢(E m, ℂ),
      eLpNorm (linearizedRestriction φ ψ y₀ f) q volume ≤ C * eLpNorm f q volume := by
  intro y₀ q hq hqp
  have hp1 : 1 < p := lt_of_le_of_lt hq hqp
  have hqtop : q ≠ ⊤ := ne_top_of_lt hqp
  set q' := q.toReal with hq'def
  have hq' : 1 ≤ q' := by
    have := ENNReal.toReal_mono hqtop hq
    simpa using this
  have hqeq : q = ENNReal.ofReal q' := (ENNReal.ofReal_toReal hqtop).symm
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · subst hm0
    have hn0 : n = 0 := by omega
    subst hn0
    exact conclusion_dim_zero φ ψ y₀ q hq
  have hL := local_estimate_of_oscillatoryOp_le φ ψ hφ hψ hψc p hp hS y₀
  by_cases hptop : p = ⊤
  · subst hptop
    exact conclusion_of_vanish φ ψ y₀ (vanish_of_top hm1 φ ψ hφ hψ hψc y₀ hL) q
  set p' := p.toReal with hp'def
  have hpeq : p = ENNReal.ofReal p' := (ENNReal.ofReal_toReal hptop).symm
  have hp' : 1 < p' := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop).2 hp1
    simpa using h
  have hqp' : q' < p' := (ENNReal.toReal_lt_toReal hqtop hptop).2 hqp
  rw [hpeq] at hL
  by_cases hp2 : 2 < p'
  · exact conclusion_of_vanish φ ψ y₀ (vanish_of_gt_two hm1 φ ψ hφ hψ hψc y₀ hp2 hL) q
  push Not at hp2
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have hm : m = 1 := by omega
    subst hm
    have hrank0 : HasConstantRank φ ψ 0 := by simpa using hrank
    exact conclusion_of_vanish φ ψ y₀ (vanish_of_rank_zero φ ψ hφ hψ hψc hrank0 y₀ hp' hL) q
  obtain ⟨r, hr1, hqr, hr2, hrlt⟩ := exists_exponent hp' hp2 hq' hqp'
  have hW := restrMu_muQ_of_local φ ψ hφ hψ hψc y₀ hp' hq' hqp' hqr hrlt hL
  obtain ⟨lam, hlam, hD⟩ := exists_scale_decayMeasure hnm hmn φ ψ hφ hψ hψc hrank p hp1 hS y₀ q' hq'
    (by rw [← hqeq]; exact hqp)
  obtain ⟨κ, α₀, hα₀, hrem⟩ := restrMu_zero_of_restrMu hm2 hD
  obtain ⟨α, hα, hαα, hkey⟩ := exists_small_alpha hq' hqr κ α₀ hα₀
  have hR := restrMu_scale_of_restrMu hlam hr1.le (hW α hα)
  have h0 := hrem r hr1 hr2 α hα hαα hR q' hq' hkey
  obtain ⟨C, hC⟩ := conclusion_of_restrMu φ ψ hφ hψ hψc y₀ hq'
    (restrMu_of_restrMu_scale hlam hq' h0)
  refine ⟨C, fun f => ?_⟩
  rw [hqeq]
  exact hC f

end TaoBR
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace
open TaoBR
open Tao49
theorem solution (n m : ℕ) (hnm : m - 1 ≤ n) (hmn : n ≤ m)
    (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry ψ)) (hψc : HasCompactSupport (Function.uncurry ψ))
    (hrank : HasConstantRank φ ψ (m - 1)) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hS : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      opNorm p p (oscillatoryOp φ ψ R) ≤
        ENNReal.ofReal (C * R ^ (-((m : ℝ) * (conjExp p)⁻¹.toReal) + ε))) :
    ∀ y₀ : E m, ∀ q : ℝ≥0∞, 1 ≤ q → q < p → ∃ C : ℝ≥0, ∀ f : 𝓢(E m, ℂ),
      eLpNorm (linearizedRestriction φ ψ y₀ f) q volume ≤ C * eLpNorm f q volume := by
  exact TaoBR.linearizedRestriction_le_of_oscillatoryOp_le_dev n m hnm hmn φ ψ hφ hψ hψc hrank p hp hS
end

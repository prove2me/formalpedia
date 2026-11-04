-- Prove2me | solution 1 for TaoBR.parabolicRestrictionConjecture_of_restrictionConjecture
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:25:17.14312+00:00
-- url     : https://prove2.me/submissions/e76bb39a-e31f-49e8-83d7-b484e5d0c45f

import Mathlib
import Definitions.Def_TaoBR
import Theorems.Thm_TaoBR_exists_sparse_cover

section S_Blueprint

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace

namespace TaoBR.Parab

/-! ## Generic objects -/

/-- The Fourier transform of a measure, `μ̂(x) = ∫ e(-⟪ξ, x⟫) dμ(ξ)` (the sphere's `sig`). -/
noncomputable def ftMeasure {n : ℕ} (μ : Measure (E n)) (x : E n) : ℂ :=
  ∫ ξ, (𝐞 (-⟪ξ, x⟫) : ℂ) ∂μ

/-- Standing hypotheses on a measure `μ` with a support set `S`: finite, carried by `S`, `S` inside
`B(0, 3/2)` (so every coordinate of a point of `S` is `≤ 3/2` and the `1/2`-cube transform does not
vanish there), the codimension-one Frostman bound `μ(B(η, r)) ≲ r^{n-1}`, and power decay of `μ̂`. -/
structure GoodMeasure {n : ℕ} (μ : Measure (E n)) (S : Set (E n)) : Prop where
  finite : IsFiniteMeasure μ
  null_compl : μ Sᶜ = 0
  subset : S ⊆ closedBall 0 (3 / 2)
  frostman : ∃ C : ℝ, ∀ η : E n, ∀ r : ℝ, 0 < r → μ (ball η r) ≤ ENNReal.ofReal (C * r ^ (n - 1))
  decay : ∃ C c : ℝ, 0 < c ∧ ∀ x : E n, ‖ftMeasure μ x‖ ≤ C * (1 + ‖x‖) ^ (-c)

/-- `R_μ(p, α)`: `‖f̂‖_{Lᵖ(μ)} ≲ R^α ‖f‖_p` for Schwartz `f` supported in `B(0, R)`, `R ≥ 1`. -/
def RestrMu {n : ℕ} (μ : Measure (E n)) (p α : ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ closedBall 0 R →
    eLpNorm (𝓕 (f : E n → ℂ)) (ENNReal.ofReal p) μ ≤
      C * ENNReal.ofReal (R ^ α) * eLpNorm f (ENNReal.ofReal p) volume

/-- The thickened estimate (the generic form of `est2`): for Schwartz `f` supported in `B(0, R)`,
`∫_{N_{1/(16R)}(S)} |f̂|^p ≤ C R^{αp} R⁻¹ ‖f‖_p^p`. -/
def ThickRestr {n : ℕ} (S : Set (E n)) (p α : ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ closedBall 0 R →
    ∫⁻ η in thickening (1 / (16 * R)) S, ‖𝓕 (f : E n → ℂ) η‖ₑ ^ p ≤
      C * ENNReal.ofReal (R ^ α) ^ p * ENNReal.ofReal (1 / R) * ∫⁻ y, ‖f y‖ₑ ^ p

/-- The bump of Lemma 3.2 (`rIn = 1/32`, `rOut = 1/16`), as in `restr_sparse_of_restr_uniform`. -/
noncomputable def bump (n : ℕ) : ContDiffBump (0 : E n) := ⟨1 / 32, 1 / 16, by norm_num, by norm_num⟩

/-- `Φ ≥ 0`, `∫ Φ = 1`, supported in `B(0, 1/16)`. -/
noncomputable def Phi (n : ℕ) (v : E n) : ℝ := (bump n).normed volume v

/-- The kernel `K(v) = R^n Φ(R v) e(-⟪v, c⟫)` (`Kernel.lean`, `K`). -/
noncomputable def Kker (n : ℕ) (R : ℝ) (c v : E n) : ℂ :=
  ((R ^ n : ℝ) : ℂ) * (Phi n (R • v) : ℂ) * (𝐞 (-⟪v, c⟫) : ℂ)

/-- The operator `T G (ω) = Σ_i ∫ K_i(ω - η) G_i(η) dη` of Lemma 3.2, now on all of `E n`. -/
noncomputable def Top {n N : ℕ} (R : ℝ) (x : Fin N → E n) (G : Fin N → E n → ℂ) (ω : E n) : ℂ :=
  ∑ i, ∫ η, Kker n R (x i) (ω - η) * G i η

/-! ## Generic ε-removal (Lemma 3.2, the p. 7 reduction, Theorem 1.2) for a good measure -/

/-! ## Sphere → paraboloid transfer -/

/-- The anisotropic dilation `(v, t) ↦ (λ v, λ² t)` of `E (m+1) = E m × ℝ`. -/
noncomputable def anisoLin {m : ℕ} (lam : ℝ) (η : E (m + 1)) : E (m + 1) :=
  mkPoint (lam • horiz η) (lam ^ 2 * vert η)

/-- The rescaling `(v, t) ↦ (λ v, λ² t - 1)`, sending the paraboloid's vertex to the south pole. -/
noncomputable def anisoMap {m : ℕ} (lam : ℝ) (η : E (m + 1)) : E (m + 1) :=
  anisoLin lam η - mkPoint 0 1

/-- The weight `w`: a smooth bump, `1` on `closedBall 0 1`, supported in `ball 0 (5/4)`. -/
noncomputable def wBump (m : ℕ) : ContDiffBump (0 : E m) := ⟨1, 5 / 4, by norm_num, by norm_num⟩

/-- `w(v)`. -/
noncomputable def wt (m : ℕ) (v : E m) : ℝ := wBump m v

/-- The graph point `(v, |v|²/2)` of the paraboloid. -/
noncomputable def graphPt {m : ℕ} (v : E m) : E (m + 1) := mkPoint v (‖v‖ ^ 2 / 2)

/-- The weighted paraboloid measure: the push-forward of `w(v) dv` under `v ↦ (v, |v|²/2)`. -/
noncomputable def parabMeasure (m : ℕ) : Measure (E (m + 1)) :=
  (volume.withDensity fun v : E m => ENNReal.ofReal (wt m v)).map graphPt

/-- Its support set: the graph over `closedBall 0 (5/4)`. -/
def parabSet (m : ℕ) : Set (E (m + 1)) := graphPt '' closedBall (0 : E m) (5 / 4)

/-- The parabolic loss `α(p) = (m+1)/p - (m+2)/2`; it vanishes at `p_c = 2(m+1)/(m+2)`. -/
noncomputable def alphaPar (m : ℕ) (p : ℝ) : ℝ := ((m : ℝ) + 1) / p - ((m : ℝ) + 2) / 2

/-! ## The paraboloid measure is good -/

/-! ## Assembly -/

end TaoBR.Parab

end S_Blueprint

section S_PartA

/-!
# Part A of the pp. 10–11 Blueprint: `top_L2` (Lemma 3.2, the `L²` bound) for a good measure

Port of `restr_sparse_of_restr_uniform` (`Kernel.lean`, `L2Aux.lean`, `TOp.lean`): the sphere
subtype is replaced by `E n` with a finite measure `μ`, `sig` by `ftMeasure μ`, the cap bound by
the Frostman bound and the sphere decay by `GoodMeasure.decay`.
-/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace


-- ASSUMED FROM BLUEPRINT
-- (none)

open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise

namespace TaoBR.Parab.PartA

/-! ## The bump `Φ` and `φ = 𝓕⁻ Φ` -/


noncomputable abbrev PhiC (n : ℕ) (v : E n) : ℂ := (Phi n v : ℂ)

noncomputable def MPhi (n : ℕ) : ℝ := 1 / (volume : Measure (E n)).real (closedBall 0 (1 / 32))

lemma Phi_nonneg (n : ℕ) (v : E n) : 0 ≤ Phi n v := (bump n).nonneg_normed v

lemma Phi_le (n : ℕ) (v : E n) : Phi n v ≤ MPhi n :=
  (bump n).normed_le_div_measure_closedBall_rIn volume v

lemma MPhi_nonneg (n : ℕ) : 0 ≤ MPhi n := (Phi_nonneg n 0).trans (Phi_le n 0)

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

/-- `φ_c(x) = φ((x - c)/R)`. -/
noncomputable def phiLoc (n : ℕ) (R : ℝ) (c : E n) (x : E n) : ℂ := phi n (R⁻¹ • (x - c))

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

variable {N : ℕ} {x : Fin N → E n}

lemma Fop_diag (hR : 1 ≤ R) (c : E n) {A1 : ℝ}
    (hcap : ∀ η : E n, ∫⁻ ω, ‖Kker n R c (ω - η)‖ₑ ∂μ ≤ ENNReal.ofReal (A1 * R))
    {G : E n → ℂ} (hGm : Measurable G) :
    ∫⁻ ω, ‖Fop n R c G ω‖ₑ ^ 2 ∂(μ) ≤
      ENNReal.ofReal (A1 * R) * ∫⁻ η, ‖G η‖ₑ ^ 2 := by
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
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_lintegral_swap (hKm.mul ((hGm.comp measurable_snd).enorm.pow_const 2)).aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono (fun η => ?_)
  rw [lintegral_mul_const' _ _ (by simp)]
  gcongr
  exact hcap η

/-- The off-diagonal constant. -/
noncomputable def Cst (μ : Measure (E n)) (Cs : ℝ) : ℝ :=
  max 1 (2 * Cs) * M0 n ^ 2 + 8 * (μ).real univ * M0 n * M1 n

lemma kern_sparse (hn : 1 ≤ n) (m : ℕ) (hm : 0 < m) (Cs : ℝ)
    (hdec : ∀ z : E n, 1 ≤ ‖z‖ → ‖ftMeasure μ z‖ ^ m * ‖z‖ ≤ Cs) (hR : 1 ≤ R) (N : ℕ) (hN : 2 ≤ N)
    (c c' : E n) (hw : (R * N) ^ (2 * n * m + 3 * n + 3) ≤ ‖c - c'‖) :
    ∫⁻ y, ∫⁻ y', ‖phiLoc n R c y‖ₑ * ‖phiLoc n R c' y'‖ₑ * ‖ftMeasure μ (y - y')‖ₑ ≤
      ENNReal.ofReal (Cst μ Cs / N) := by
  have hR0 : 0 < R := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set X := R * (N : ℝ) with hX
  have hX2 : 2 ≤ X := by nlinarith
  have hX1 : 1 ≤ X := by linarith
  set C0 := 2 * n * m + 3 * n + 3
  set w := c - c'
  set Q := R ^ (2 * n) * (N : ℝ) with hQ
  have hQ1 : 1 ≤ Q := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR) hN1
  have hw2 : 2 ≤ ‖w‖ := le_trans (le_trans hX2 (le_self_pow₀ hX1 (by omega))) hw
  have hw0 : 0 < ‖w‖ := by linarith
  have hQw : Q ^ m ≤ ‖w‖ := by
    calc Q ^ m = R ^ (2 * n * m) * (N : ℝ) ^ m := by rw [hQ, mul_pow, ← pow_mul]
      _ ≤ R ^ (2 * n * m) * (N : ℝ) ^ (2 * n * m) := by
          gcongr
          nlinarith
      _ = X ^ (2 * n * m) := by rw [hX, mul_pow]
      _ ≤ X ^ C0 := pow_le_pow_right₀ hX1 (by omega)
      _ ≤ ‖w‖ := hw
  have hRw : R ^ (2 * n + 1) * N ≤ ‖w‖ := by
    calc R ^ (2 * n + 1) * (N : ℝ) ≤ R ^ (2 * n + 1) * (N : ℝ) ^ (2 * n + 1) := by
          gcongr; exact le_self_pow₀ hN1 (by omega)
      _ = X ^ (2 * n + 1) := by rw [hX, mul_pow]
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
  have t1 : D / Q * (R ^ n * M0 n) ^ 2 = D * M0 n ^ 2 / N := by
    rw [hQ, mul_pow, ← pow_mul]; field_simp; ring
  have t2 : 4 * s / ‖w‖ * (2 * R ^ (2 * n + 1) * M0 n * M1 n) ≤
      8 * s * M0 n * M1 n / N := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hw0 hN0]
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
    (hdec : ∀ z : E n, 1 ≤ ‖z‖ → ‖ftMeasure μ z‖ ^ m * ‖z‖ ≤ Cs) (hR : 1 ≤ R) {A1 : ℝ} (hA1 : 0 ≤ A1)
    (hcap : ∀ c η : E n, ∫⁻ ω, ‖Kker n R c (ω - η)‖ₑ ∂μ ≤ ENNReal.ofReal (A1 * R))
    (V : ℝ) (hV : 0 ≤ V)
    (hsp : ∀ i j, i ≠ j → (R * N) ^ (2 * n * m + 3 * n + 3) ≤ ‖x i - x j‖)
    (G : Fin N → E n → ℂ) (hGi : ∀ i, Integrable (G i)) (hGs : ∀ i, StronglyMeasurable (G i))
    (hL2 : ∀ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 ≠ ⊤)
    (hL1 : ∀ i, (∫⁻ η, ‖G i η‖ₑ) ^ 2 ≤ ENNReal.ofReal V * ∫⁻ η, ‖G i η‖ₑ ^ 2) :
    ∫⁻ ω, ‖Top R x G ω‖ₑ ^ 2 ∂(μ) ≤
      ENNReal.ofReal ((A1 + Cst μ Cs * V) * R) * ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 := by
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
  have hdiag : ∀ i, (∫ ω, F i ω * conj (F i ω) ∂σ).re ≤ A1 * R * b i := by
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
    have hd := Fop_diag hR (x i) (hcap (x i)) (hGs i).measurable
    rw [hB i, ← ENNReal.ofReal_mul (by have := hA1; positivity)] at hd
    calc _ ≤ (ENNReal.ofReal (A1 * R * b i)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
      _ = _ := ENNReal.toReal_ofReal (by have := hA1; have := hb0 i; positivity)
  have hC := Cst_nonneg μ Cs
  have hoff : ∀ i j, i ≠ j →
      (∫ ω, F i ω * conj (F j ω) ∂σ).re ≤ Cst μ Cs / N * (a i * a j) := by
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
      ∑ i, ∑ j, ((if i = j then A1 * R * b i else 0) + Cst μ Cs / N * (a i * a j)) := by
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      have := hdiag i
      have : 0 ≤ Cst μ Cs / N * (a i * a i) := by
        have := ha0 i; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; positivity
      linarith
    · simp only [hij, if_false, zero_add]
      exact hoff i j hij
  have hcomb : ∑ i, ∑ j, ((if i = j then A1 * R * b i else 0) + Cst μ Cs / N * (a i * a j)) =
      A1 * R * ∑ i, b i + Cst μ Cs / N * (∑ i, a i) ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.mul_sum, sq, Finset.sum_mul_sum]
  have hCS : Cst μ Cs / N * (∑ i, a i) ^ 2 ≤ Cst μ Cs * V * ∑ i, b i := by
    have h1 : (∑ i, a i) ^ 2 ≤ N * ∑ i, a i ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
    have h2 : ∑ i, a i ^ 2 ≤ V * ∑ i, b i := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun i _ => hab i)
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_mul_eq_mul_div, div_le_iff₀ hN0]
      calc Cst μ Cs * (∑ i, a i) ^ 2 ≤ Cst μ Cs * (N * (V * ∑ i, b i)) := by
            gcongr; exact h1.trans (by gcongr)
        _ = _ := by ring
  have hbn : 0 ≤ ∑ i, b i := Finset.sum_nonneg (fun i _ => hb0 i)
  rw [hLHS]
  calc ENNReal.ofReal (∑ i, ∑ j, (∫ ω, F i ω * conj (F j ω) ∂σ).re)
      ≤ ENNReal.ofReal ((A1 + Cst μ Cs * V) * R * ∑ i, b i) := by
        apply ENNReal.ofReal_le_ofReal
        have hcv : 0 ≤ Cst μ Cs * V * ∑ i, b i := by positivity
        have : Cst μ Cs * V * ∑ i, b i ≤ Cst μ Cs * V * R * ∑ i, b i := by nlinarith
        nlinarith [hsum, hcomb, hCS]
    _ = _ := by
        rw [ENNReal.ofReal_mul (by have := hA1; positivity),
          ENNReal.ofReal_sum_of_nonneg (fun i _ => hb0 i)]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => (hB i).symm)

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

/-! ## The diagonal (cap) bound from Frostman -/

/-- The `L¹` constant: `R^n sup Φ · C_F (16R)^{-(n-1)} = A1 · R`. -/
noncomputable def A1 (n : ℕ) (CF : ℝ) : ℝ := MPhi n * max CF 0 * (1 / 16) ^ (n - 1)

omit [IsFiniteMeasure μ] in
lemma A1_nonneg (n : ℕ) (CF : ℝ) : 0 ≤ A1 n CF := by
  unfold A1; have := MPhi_nonneg n; positivity

omit [IsFiniteMeasure μ] in
lemma K_cap (hn : 1 ≤ n) (hR : 1 ≤ R) {CF : ℝ}
    (hF : ∀ η : E n, ∀ r : ℝ, 0 < r → μ (ball η r) ≤ ENNReal.ofReal (CF * r ^ (n - 1)))
    (c η : E n) :
    ∫⁻ ω, ‖Kker n R c (ω - η)‖ₑ ∂μ ≤ ENNReal.ofReal (A1 n CF * R) := by
  have hR0 : 0 < R := by linarith
  set r := 1 / (16 * R)
  have hpt : ∀ ω : E n, ‖Kker n R c (ω - η)‖ₑ ≤
      (ball η r).indicator (fun _ => ENNReal.ofReal (R ^ n * MPhi n)) ω := by
    intro ω
    by_cases hK : Kker n R c (ω - η) = 0
    · rw [hK, enorm_zero]; exact bot_le
    · have hmem : ω ∈ ball η r := by
        have := K_support hR0 hK
        rw [mem_ball, dist_eq_norm]; exact this
      rw [indicator_of_mem hmem, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (K_norm_le hR0 _)
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_indicator_const measurableSet_ball]
  have hc : μ (ball η r) ≤ ENNReal.ofReal (max CF 0 * r ^ (n - 1)) :=
    (hF η r (by positivity)).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  calc ENNReal.ofReal (R ^ n * MPhi n) * μ (ball η r)
      ≤ ENNReal.ofReal (R ^ n * MPhi n) * ENNReal.ofReal (max CF 0 * r ^ (n - 1)) := by gcongr
    _ = ENNReal.ofReal (A1 n CF * R) := ?_
  rw [← ENNReal.ofReal_mul (by have := MPhi_nonneg n; positivity)]
  congr 1
  simp only [A1, r]
  have hn1 : R ^ n = R * R ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  rw [hn1, div_pow, mul_pow, one_pow, div_pow, one_pow]
  have : R ^ (n - 1) ≠ 0 := by positivity
  field_simp

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

/-! ## Restriction to `B(0, 2)` and the main bound -/

omit [IsFiniteMeasure μ] in
lemma Top_eq_restrict (hR : 1 ≤ R) (G : Fin N → E n → ℂ) (hG : ∀ i, Integrable (G i))
    {ω : E n} (hω : ‖ω‖ ≤ 3 / 2) :
    Top R x G ω = Top R x (fun i => (closedBall (0 : E n) 2).indicator
      ((hG i).aestronglyMeasurable.mk (G i))) ω := by
  have hR0 : 0 < R := by linarith
  unfold Top
  refine Finset.sum_congr rfl (fun i _ => integral_congr_ae ?_)
  filter_upwards [(hG i).aestronglyMeasurable.ae_eq_mk] with η hη
  by_cases hK : Kker n R (x i) (ω - η) = 0
  · simp [hK]
  · have h1 := K_support hR0 hK
    have h2 : 1 / (16 * R) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    have hmem : η ∈ closedBall (0 : E n) 2 := by
      rw [mem_closedBall_zero_iff]
      have := norm_sub_le ω (ω - η)
      rw [sub_sub_cancel] at this
      linarith
    simp only [indicator_of_mem hmem, hη]

/-- **G1 (Lemma 3.2, the `L²` bound).** Verbatim restatement of the Blueprint's `top_L2`. -/
theorem top_L2 {n : ℕ} (hn : 2 ≤ n) {μ : Measure (E n)} {S : Set (E n)} (hμ : GoodMeasure μ S) :
    ∃ C0 : ℕ, 3 * n + 3 ≤ C0 ∧ ∃ A2 : ℝ, 0 ≤ A2 ∧
      ∀ R : ℝ, 1 ≤ R → ∀ (N : ℕ) (x : Fin N → E n), IsSparse (C0 : ℝ) R x →
        ∀ G : Fin N → E n → ℂ, (∀ i, Integrable (G i)) → (∀ i, MemLp (G i) 2) →
          ∫⁻ ω, ‖Top R x G ω‖ₑ ^ (2 : ℝ) ∂μ ≤
            ENNReal.ofReal (A2 * R) * ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ (2 : ℝ) := by
  have := hμ.finite
  obtain ⟨CF, hF⟩ := hμ.frostman
  obtain ⟨Cd, c, hc, hdec0⟩ := hμ.decay
  obtain ⟨m, hm, Cs, hdec⟩ := decay_conv hc hdec0
  have hS : ∀ᵐ ω ∂μ, ω ∈ S := mem_ae_iff.2 hμ.null_compl
  set V := (volume : Measure (E n)).real (closedBall 0 2)
  have hV : 0 ≤ V := measureReal_nonneg
  refine ⟨2 * n * m + 3 * n + 3, by omega, A1 n CF + Cst μ Cs * V,
    by have := A1_nonneg n CF; have := Cst_nonneg μ Cs; positivity, ?_⟩
  intro R hR N x hsp G hGi hGL2
  set G' : Fin N → E n → ℂ := fun i => (closedBall (0 : E n) 2).indicator
    ((hGi i).aestronglyMeasurable.mk (G i)) with hG'
  have hGs' : ∀ i, StronglyMeasurable (G' i) := fun i =>
    (hGi i).aestronglyMeasurable.stronglyMeasurable_mk.indicator measurableSet_closedBall
  have hGi' : ∀ i, Integrable (G' i) := fun i =>
    ((hGi i).congr (hGi i).aestronglyMeasurable.ae_eq_mk).indicator measurableSet_closedBall
  have hG'le : ∀ i, ∫⁻ η, ‖G' i η‖ₑ ^ 2 ≤ ∫⁻ η, ‖G i η‖ₑ ^ 2 := by
    intro i
    refine lintegral_mono_ae ?_
    filter_upwards [(hGi i).aestronglyMeasurable.ae_eq_mk] with η hη
    by_cases h : η ∈ closedBall (0 : E n) 2
    · simp only [G', indicator_of_mem h, ← hη, le_refl]
    · simp [G', indicator_of_notMem h]
  have hfin : ∀ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 ≠ ⊤ := by
    intro i
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
      (hGL2 i).eLpNorm_lt_top
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at this
    exact this.ne
  have hL1 : ∀ i, (∫⁻ η, ‖G' i η‖ₑ) ^ 2 ≤ ENNReal.ofReal V * ∫⁻ η, ‖G' i η‖ₑ ^ 2 := by
    intro i
    refine l1_l2_ball (G' i) (hGs' i).measurable (fun η h => ?_)
    simp [G', indicator_of_notMem h]
  have hsp' : ∀ i j, i ≠ j → (R * N) ^ (2 * n * m + 3 * n + 3) ≤ ‖x i - x j‖ := by
    intro i j h
    have := hsp i j h
    rwa [Real.rpow_natCast, Real.rpow_natCast, ← mul_pow, dist_eq_norm] at this
  have hcongr : ∫⁻ ω, ‖Top R x G ω‖ₑ ^ (2 : ℝ) ∂μ = ∫⁻ ω, ‖Top R x G' ω‖ₑ ^ (2 : ℝ) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hS] with ω hω
    have hω' : ‖ω‖ ≤ 3 / 2 := mem_closedBall_zero_iff.1 (hμ.subset hω)
    rw [Top_eq_restrict hR G hGi hω']
  rw [hcongr]
  simp only [ENNReal.rpow_two]
  refine (Top_L2_core (by omega) m hm Cs hdec hR (A1_nonneg n CF)
    (fun c η => K_cap (by omega) hR hF c η) V hV hsp' G' hGi' hGs'
    (fun i => ne_top_of_le_ne_top (hfin i) (hG'le i)) hL1).trans ?_
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hG'le i)) (by positivity)

end TaoBR.Parab.PartA

end S_PartA

namespace TaoBR.Parab
alias top_L2 := TaoBR.Parab.PartA.top_L2
end TaoBR.Parab

section S_PartB

/-!
# Part B of the pp. 10–11 Blueprint: `sparse_of_thick` (Lemma 3.2, assembly) for a good measure

Port of `restr_sparse_of_restr_uniform` (`Marc.lean`, `Decomp.lean`, `Kernel.lean`, `TOp.lean`,
`Main.lean`): the sphere's annulus becomes the thickening `N_{1/(16R)}(S)`, `est2` becomes the
hypothesis `ThickRestr S p α` (applied to the translates of the pieces), and the cap bound becomes
the Frostman bound of `GoodMeasure`.
-/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace


-- ASSUMED FROM BLUEPRINT
-- (none)

open MeasureTheory Metric Set Filter Topology
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
  Pointwise

namespace TaoBR.Parab.PartB

/-! ## The bump `Φ` and `φ = 𝓕⁻ Φ` -/


noncomputable abbrev PhiC (n : ℕ) (v : E n) : ℂ := (Phi n v : ℂ)

noncomputable def MPhi (n : ℕ) : ℝ := 1 / (volume : Measure (E n)).real (closedBall 0 (1 / 32))

lemma Phi_nonneg (n : ℕ) (v : E n) : 0 ≤ Phi n v := (bump n).nonneg_normed v

lemma Phi_le (n : ℕ) (v : E n) : Phi n v ≤ MPhi n :=
  (bump n).normed_le_div_measure_closedBall_rIn volume v

lemma MPhi_nonneg (n : ℕ) : 0 ≤ MPhi n := (Phi_nonneg n 0).trans (Phi_le n 0)

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

lemma phi_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (phi n) := (phiS n).smooth ⊤

lemma Phi_integrable (n : ℕ) : Integrable (Phi n) := (bump n).integrable_normed
/-- `φ_c(x) = φ((x - c)/R)`. -/
noncomputable def phiLoc (n : ℕ) (R : ℝ) (c : E n) (x : E n) : ℂ := phi n (R⁻¹ • (x - c))

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

end TaoBR.Parab.PartB

namespace TaoBR.Parab.PartB

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

section MarcSec

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

end MarcSec


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

end TaoBR.Parab.PartB

namespace TaoBR.Parab.PartB

/-! ## The operator `T` against a measure on `E n` -/

section TopSec

variable {n : ℕ} {N : ℕ} {R : ℝ} {x : Fin N → E n}

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

/-- The `L¹` constant: `R^n sup Φ · C_F (16R)^{-(n-1)} = A1 · R`. -/
noncomputable def A1 (n : ℕ) (CF : ℝ) : ℝ := MPhi n * max CF 0 * (1 / 16) ^ (n - 1)

lemma A1_nonneg (n : ℕ) (CF : ℝ) : 0 ≤ A1 n CF := by
  unfold A1; have := MPhi_nonneg n; positivity

lemma K_cap {μ : Measure (E n)} (hn : 1 ≤ n) (hR : 1 ≤ R) {CF : ℝ}
    (hF : ∀ η : E n, ∀ r : ℝ, 0 < r → μ (ball η r) ≤ ENNReal.ofReal (CF * r ^ (n - 1)))
    (c η : E n) :
    ∫⁻ ω, ‖Kker n R c (ω - η)‖ₑ ∂μ ≤ ENNReal.ofReal (A1 n CF * R) := by
  have hR0 : 0 < R := by linarith
  set r := 1 / (16 * R)
  have hpt : ∀ ω : E n, ‖Kker n R c (ω - η)‖ₑ ≤
      (ball η r).indicator (fun _ => ENNReal.ofReal (R ^ n * MPhi n)) ω := by
    intro ω
    by_cases hK : Kker n R c (ω - η) = 0
    · rw [hK, enorm_zero]; exact bot_le
    · have hmem : ω ∈ ball η r := by
        have := K_support hR0 hK
        rw [mem_ball, dist_eq_norm]; exact this
      rw [indicator_of_mem hmem, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (K_norm_le hR0 _)
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_indicator_const measurableSet_ball]
  have hc : μ (ball η r) ≤ ENNReal.ofReal (max CF 0 * r ^ (n - 1)) :=
    (hF η r (by positivity)).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  calc ENNReal.ofReal (R ^ n * MPhi n) * μ (ball η r)
      ≤ ENNReal.ofReal (R ^ n * MPhi n) * ENNReal.ofReal (max CF 0 * r ^ (n - 1)) := by gcongr
    _ = ENNReal.ofReal (A1 n CF * R) := ?_
  rw [← ENNReal.ofReal_mul (by have := MPhi_nonneg n; positivity)]
  congr 1
  simp only [A1, r]
  have hn1 : R ^ n = R * R ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  rw [hn1, div_pow, mul_pow, one_pow, div_pow, one_pow]
  have : R ^ (n - 1) ≠ 0 := by positivity
  field_simp

lemma Top_L1 {μ : Measure (E n)} [SFinite μ] (hn : 1 ≤ n) (hR : 1 ≤ R) {CF : ℝ}
    (hF : ∀ η : E n, ∀ r : ℝ, 0 < r → μ (ball η r) ≤ ENNReal.ofReal (CF * r ^ (n - 1)))
    (G : Fin N → E n → ℂ) (hG : ∀ i, Measurable (G i)) :
    ∫⁻ ω, ‖Top R x G ω‖ₑ ∂μ ≤ ENNReal.ofReal (A1 n CF * R) * ∑ i, ∫⁻ η, ‖G i η‖ₑ := by
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
  rw [lintegral_finsetSum _ hmi, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [lintegral_lintegral_swap (hm i).aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono (fun η => ?_)
  rw [lintegral_mul_const' _ _ enorm_ne_top]
  gcongr
  exact K_cap hn hR hF (x i) η

end TopSec

/-! ## The thickening and the input class -/

section MainSec

variable {n : ℕ} {R : ℝ} {N : ℕ}

/-- The thickening `N_{1/(16R)}(S)`. -/
abbrev Th (S : Set (E n)) (R : ℝ) : Set (E n) := thickening (1 / (16 * R)) S

lemma Th_subset {S : Set (E n)} (hS : S ⊆ closedBall 0 (3 / 2)) (hR : 1 ≤ R) :
    Th S R ⊆ closedBall 0 2 := by
  intro η hη
  obtain ⟨z, hz, hd⟩ := mem_thickening_iff.1 hη
  have h1 : dist z 0 ≤ 3 / 2 := hS hz
  have h2 : 1 / (16 * R) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  rw [mem_closedBall]
  linarith [dist_triangle η z 0]

lemma Th_measurable {S : Set (E n)} : MeasurableSet (Th S R) :=
  isOpen_thickening.measurableSet

/-- The class of inputs: measurable, bounded, supported in the thickening. -/
def PG (S : Set (E n)) (R : ℝ) {N : ℕ} (G : Fin N → E n → ℂ) : Prop :=
  ∀ i, Measurable (G i) ∧ (∃ B : ℝ, ∀ η, ‖G i η‖ ≤ B) ∧ ∀ η ∉ Th S R, G i η = 0

variable {S : Set (E n)}

lemma PG_eq_indicator {G : Fin N → E n → ℂ} (hS : S ⊆ closedBall 0 (3 / 2)) (hR : 1 ≤ R)
    (hG : PG S R G) (i : Fin N) :
    G i = (closedBall (0 : E n) 2).indicator (G i) := by
  funext η
  by_cases h : η ∈ closedBall (0 : E n) 2
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h, (hG i).2.2 η (fun h' => h (Th_subset hS hR h'))]

lemma PG_integrable {G : Fin N → E n → ℂ} (hS : S ⊆ closedBall 0 (3 / 2)) (hR : 1 ≤ R)
    (hG : PG S R G) (i : Fin N) : Integrable (G i) := by
  obtain ⟨B, hB⟩ := (hG i).2.1
  rw [PG_eq_indicator hS hR hG i, integrable_indicator_iff measurableSet_closedBall]
  exact Measure.integrableOn_of_bounded (M := B) measure_closedBall_lt_top.ne
    (hG i).1.aestronglyMeasurable (Eventually.of_forall hB)

lemma PG_memLp {G : Fin N → E n → ℂ} (hS : S ⊆ closedBall 0 (3 / 2)) (hR : 1 ≤ R)
    (hG : PG S R G) (i : Fin N) : MemLp (G i) 2 := by
  obtain ⟨B, hB⟩ := (hG i).2.1
  rw [PG_eq_indicator hS hR hG i, memLp_indicator_iff_restrict measurableSet_closedBall]
  have : IsFiniteMeasure (volume.restrict (closedBall (0 : E n) 2)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  exact MemLp.of_bound (hG i).1.aestronglyMeasurable B (Eventually.of_forall hB)

lemma PG_truncHi {G : Fin N → E n → ℂ} (hG : PG S R G) (t : ℝ) : PG S R (truncHi G t) := by
  intro i
  obtain ⟨hm, ⟨B, hB⟩, hs⟩ := hG i
  refine ⟨Measurable.ite (measurableSet_lt measurable_const hm.norm) hm measurable_const,
    ⟨max B 0, fun η => ?_⟩, fun η hη => ?_⟩
  · simp only [truncHi]; split_ifs
    · exact (hB η).trans (le_max_left _ _)
    · simp
  · simp only [truncHi, hs η hη]; simp

lemma PG_truncLo {G : Fin N → E n → ℂ} (hG : PG S R G) (t : ℝ) : PG S R (truncLo G t) := by
  intro i
  obtain ⟨hm, ⟨B, hB⟩, hs⟩ := hG i
  refine ⟨Measurable.ite (measurableSet_lt measurable_const hm.norm) measurable_const hm,
    ⟨max B 0, fun η => ?_⟩, fun η hη => ?_⟩
  · simp only [truncLo]; split_ifs
    · simp
    · exact (hB η).trans (le_max_left _ _)
  · simp only [truncLo, hs η hη]; simp

lemma mem_Th_of_K (hR : 1 ≤ R) {c ω η : E n} (hω : ω ∈ S)
    (h : Kker n R c (ω - η) ≠ 0) : η ∈ Th S R := by
  have h1 := K_support (by linarith) h
  rw [Th, mem_thickening_iff]
  exact ⟨ω, hω, by rw [dist_eq_norm, ← norm_neg, neg_sub]; exact h1⟩

lemma fourier_eq_Top (hR : 1 ≤ R) (x : Fin N → E n) (f : 𝓢(E n, ℂ))
    (g : Fin N → 𝓢(E n, ℂ)) (hgs : ∀ i, tsupport (g i) ⊆ closedBall (x i) R)
    (hfg : ∀ y, f y = ∑ i, g i y * phiLoc n R (x i) y) {ω : E n} (hω : ω ∈ S) :
    𝓕 (f : E n → ℂ) ω = Top R x (fun i => (Th S R).indicator (𝓕 (g i : E n → ℂ))) ω := by
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
    rw [indicator_of_mem (mem_Th_of_K hR hω hK)]

lemma PG_G (hR : 1 ≤ R) (g : Fin N → 𝓢(E n, ℂ)) :
    PG S R (fun i => (Th S R).indicator (𝓕 (g i : E n → ℂ))) := by
  intro i
  have hcont : Continuous (𝓕 (g i : E n → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 (g i)).continuous
  refine ⟨hcont.measurable.indicator Th_measurable, ⟨∫ y, ‖g i y‖, fun η => ?_⟩,
    fun η hη => indicator_of_notMem hη _⟩
  dsimp only
  by_cases h : η ∈ Th S R
  · rw [indicator_of_mem h]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  · rw [indicator_of_notMem h, norm_zero]
    exact integral_nonneg (fun _ => norm_nonneg _)

lemma sum_G_bound {q : ℝ} (hq : 0 < q) (g : Fin N → 𝓢(E n, ℂ)) :
    ∑ i, ∫⁻ η, ‖(Th S R).indicator (𝓕 (g i : E n → ℂ)) η‖ₑ ^ q =
      ∑ i, ∫⁻ η in Th S R, ‖𝓕 (g i : E n → ℂ) η‖ₑ ^ q := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← lintegral_indicator Th_measurable]
  congr 1; ext η
  by_cases h : η ∈ Th S R
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h, ENNReal.zero_rpow_of_pos hq]

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

end MainSec

/-- **G2 (Lemma 3.2, assembly).** Verbatim restatement of the Blueprint's `sparse_of_thick`. -/
theorem sparse_of_thick {n : ℕ} (hn : 2 ≤ n) {μ : Measure (E n)} {S : Set (E n)}
    (hμ : GoodMeasure μ S) {C0 : ℕ} (hC0 : 3 * n + 3 ≤ C0) {A2 : ℝ} (hA2 : 0 ≤ A2)
    (hL2 : ∀ R : ℝ, 1 ≤ R → ∀ (N : ℕ) (x : Fin N → E n), IsSparse (C0 : ℝ) R x →
      ∀ G : Fin N → E n → ℂ, (∀ i, Integrable (G i)) → (∀ i, MemLp (G i) 2) →
        ∫⁻ ω, ‖Top R x G ω‖ₑ ^ (2 : ℝ) ∂μ ≤
          ENNReal.ofReal (A2 * R) * ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ (2 : ℝ))
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2) {α : ℝ} (hα : 0 ≤ α) (hT : ThickRestr S p α) :
    ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ (N : ℕ) (x : Fin N → E n), IsSparse (C0 : ℝ) R x →
      ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ ⋃ i, closedBall (x i) R →
        eLpNorm (𝓕 (f : E n → ℂ)) (ENNReal.ofReal p) μ ≤
          C * ENNReal.ofReal (R ^ α) * eLpNorm f (ENNReal.ofReal p) volume := by
  have := hμ.finite
  obtain ⟨CF, hF⟩ := hμ.frostman
  obtain ⟨C2, hC2⟩ := hT
  have hS : ∀ᵐ ω ∂μ, ω ∈ S := mem_ae_iff.2 hμ.null_compl
  have hq0 : 0 < p := by linarith
  have hA1 : 0 ≤ A1 n CF := A1_nonneg n CF
  set A := A1 n CF + A2 with hA_def
  set Cm := ENNReal.ofReal (p * (2 / (p - 1) + 4 / (2 - p))) with hCm
  set K0 : ℝ≥0∞ := Cm * ENNReal.ofReal A * C2 * 2 ^ p with hK0_def
  have hK0 : K0 ≠ ⊤ := by
    simp only [hK0_def]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top) ENNReal.coe_ne_top) ?_
    exact ENNReal.rpow_ne_top_of_nonneg hq0.le (by simp)
  refine ⟨(K0 ^ (1 / p)).toNNReal, ?_⟩
  intro R hR N x hx f hf
  have hR0 : 0 < R := by linarith
  obtain ⟨g, hgs, hfg, hgsum⟩ := decomp n hn hR x (isSparse_mono hR hC0 hx) f hf hq0
  set G : Fin N → E n → ℂ := fun i => (Th S R).indicator (𝓕 (g i : E n → ℂ)) with hG_def
  have hPG : PG S R G := PG_G hR g
  have hSub := hμ.subset
  have hmarc := marc (volume : Measure (E n)) μ (PG S R) (Top R x)
    (ENNReal.ofReal (A * R)) (fun G t hG => PG_truncHi hG t) (fun G t hG => PG_truncLo hG t)
    (fun G G' hG hG' => Top_add hR0 G G' (PG_integrable hSub hR hG) (PG_integrable hSub hR hG'))
    (fun G hG => Top_meas G (fun i => (hG i).1)) (fun G hG i => (hG i).1)
    (fun G hG => (Top_L1 (by omega) hR hF G (fun i => (hG i).1)).trans (by
      gcongr; nlinarith))
    (fun G hG => (hL2 R hR N x hx G (PG_integrable hSub hR hG) (PG_memLp hSub hR hG)).trans (by
      gcongr; nlinarith))
    hp hp2 G hPG
  have hTG : ∫⁻ ω, ‖𝓕 (f : E n → ℂ) ω‖ₑ ^ p ∂μ = ∫⁻ ω, ‖Top R x G ω‖ₑ ^ p ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hS] with ω hω
    rw [fourier_eq_Top hR x f g hgs hfg hω]
  rw [← hTG] at hmarc
  -- bound the inputs
  have hin : ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ p ≤
      C2 * ENNReal.ofReal (R ^ α) ^ p * ENNReal.ofReal (1 / R) * ((2 : ℝ≥0∞) ^ p *
        ∫⁻ y, ‖f y‖ₑ ^ p) := by
    rw [hG_def, sum_G_bound hq0 g]
    calc ∑ i, ∫⁻ η in Th S R, ‖𝓕 (g i : E n → ℂ) η‖ₑ ^ p
        ≤ ∑ i, C2 * ENNReal.ofReal (R ^ α) ^ p * ENNReal.ofReal (1 / R) *
            ∫⁻ y, ‖g i y‖ₑ ^ p := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          obtain ⟨h, hhs, hhF, hhL⟩ := exists_translate (g i) (x i) (hgs i)
          have e1 : ∫⁻ η in Th S R, ‖𝓕 (g i : E n → ℂ) η‖ₑ ^ p =
              ∫⁻ η in Th S R, ‖𝓕 (h : E n → ℂ) η‖ₑ ^ p := by
            simp_rw [hhF]
          rw [e1, ← hhL p]
          exact hC2 R hR h hhs
      _ = C2 * ENNReal.ofReal (R ^ α) ^ p * ENNReal.ofReal (1 / R) *
            ∑ i, ∫⁻ y, ‖g i y‖ₑ ^ p := by rw [Finset.mul_sum]
      _ ≤ _ := by gcongr
  have htot : ∫⁻ ω, ‖𝓕 (f : E n → ℂ) ω‖ₑ ^ p ∂μ ≤
      K0 * ENNReal.ofReal (R ^ α) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p := by
    refine hmarc.trans ?_
    calc Cm * ENNReal.ofReal (A * R) * ∑ i, ∫⁻ η, ‖G i η‖ₑ ^ p
        ≤ Cm * ENNReal.ofReal (A * R) * (C2 * ENNReal.ofReal (R ^ α) ^ p *
            ENNReal.ofReal (1 / R) * ((2 : ℝ≥0∞) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p)) := by gcongr
      _ = Cm * (ENNReal.ofReal (A * R) * ENNReal.ofReal (1 / R)) * C2 * 2 ^ p *
            ENNReal.ofReal (R ^ α) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p := by ring
      _ = K0 * ENNReal.ofReal (R ^ α) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p := by
          rw [← ENNReal.ofReal_mul (by nlinarith), mul_assoc A, mul_one_div_cancel hR0.ne',
            mul_one]
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

end TaoBR.Parab.PartB

end S_PartB

namespace TaoBR.Parab
alias sparse_of_thick := TaoBR.Parab.PartB.sparse_of_thick
end TaoBR.Parab

section S_PartC

/-!
# Part C of the pp. 10–11 Blueprint: `restrMu_zero_of_cubeUnion_bound` (the p. 7 reduction)

Port of `proofs/restr_zero_of_cubeUnion_bound/Solution.lean`: the sphere measure on the subtype is
replaced by a finite measure `μ` on `E n` carried by `S ⊆ closedBall 0 (3/2)`, `𝓕 f` by
`𝓕 f`, and the lower bound for the transform of the `1/2`-cube is taken on `closedBall 0 (3/2)`.
-/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace


-- ASSUMED FROM BLUEPRINT
-- (nothing: Part C uses no other Blueprint lemma)

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.Parab.PartC

variable {n : ℕ}

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

end TaoBR.Parab.PartC

end
end

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.Parab.PartC

variable {n : ℕ}

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

end TaoBR.Parab.PartC

end
end

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.Parab.PartC

variable {n : ℕ}

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

end TaoBR.Parab.PartC

end
end

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.Parab.PartC

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

section Main


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

end Main

end TaoBR.Parab.PartC

end
end

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.Parab.PartC

variable {n : ℕ} {μ : Measure (E n)}

section Main

variable {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {q q₀ A : ℝ} (hq : 1 ≤ q) (hqq : q < q₀) (hA : 0 ≤ A)
  (h4 : ∀ t : Finset (Fin n → ℤ), eLpNorm (cubeSum c t (fun _ => 1)) (ENNReal.ofReal q)
      μ ≤ ENNReal.ofReal (A * ((t.card : ℝ) * c ^ n) ^ (1 / q₀)))
include hc hq hqq hA h4

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

end Main

end TaoBR.Parab.PartC

end
end

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.Parab.PartC

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

end TaoBR.Parab.PartC

end
end

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.Parab.PartC

variable {n : ℕ}

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

end TaoBR.Parab.PartC

end
end

section
section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace

namespace TaoBR.Parab.PartC

variable {n : ℕ} {μ : Measure (E n)} [IsFiniteMeasure μ]


section Main

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

end Main

end TaoBR.Parab.PartC

end
end

section
open MeasureTheory Metric Real
open scoped FourierTransform ENNReal NNReal RealInnerProductSpace SchwartzMap

namespace TaoBR.Parab.PartC

/-- **G3 (the p. 7 reduction, `c = 1/2`).** A bound for indicators of unions of `1/2`-cubes gives
`R_μ(q, 0)` for every `q < q₀`. -/
theorem restrMu_zero_of_cubeUnion_bound {n : ℕ} (hn : 2 ≤ n) {μ : Measure (E n)} {S : Set (E n)}
    (hμ : GoodMeasure μ S) (p : ℝ) (q₀ : ℝ) (hq₀ : 1 < q₀) (hq₀p : q₀ ≤ p)
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

end TaoBR.Parab.PartC

end

end S_PartC

namespace TaoBR.Parab
alias restrMu_zero_of_cubeUnion_bound := TaoBR.Parab.PartC.restrMu_zero_of_cubeUnion_bound
end TaoBR.Parab

section S_PartD

/-!
# Part D of the pp. 10–11 Blueprint: `restrMu_zero_of_thick` (Theorem 1.2) for a good measure

Port of `proofs/restr_zero_of_restr/Solution.lean`: the sphere's `restriction` becomes `𝓕 ·` on the
finite measure `μ`; the sparse estimate comes from `top_L2` and `sparse_of_thick`, the cube reduction
from `restrMu_zero_of_cubeUnion_bound`. The separation exponent `C0` of `top_L2` does not depend on
`p` or `α`, so `κ` and `α₀` are chosen before `p`.
-/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace


section
open MeasureTheory Metric
open scoped FourierTransform ENNReal NNReal SchwartzMap ContDiff RealInnerProductSpace

namespace TaoBR.Parab.PartD

variable {n : ℕ}

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
theorem restrMu_zero_of_thick {n : ℕ} (hn : 2 ≤ n) {μ : Measure (E n)} {S : Set (E n)}
    (hμ : GoodMeasure μ S) :
    ∃ κ α₀ : ℝ, 0 < α₀ ∧ ∀ p : ℝ, 1 < p → p < 2 → ∀ α : ℝ, 0 < α → α < α₀ →
      ThickRestr S p α → ∀ q : ℝ, 1 ≤ q → 1 / p + κ / Real.log (1 / α) < 1 / q →
        RestrMu μ q 0 := by
  have := hμ.finite
  obtain ⟨C0, hC0, A2, hA2, hL2⟩ := top_L2 hn hμ
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
  obtain ⟨C, hC⟩ := sparse_of_thick hn hμ hC0 hA2 hL2 hp hp2 hα.le hT
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

end TaoBR.Parab.PartD

end

section
open TaoBR.Parab
end

end S_PartD

namespace TaoBR.Parab
alias restrMu_zero_of_thick := TaoBR.Parab.PartD.restrMu_zero_of_thick
end TaoBR.Parab

section S_PartE

/-! # Part E: `annulus_of_restr` (annulus estimate from spherical `R(p, 0)`) and `map_anisoLin` -/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace


namespace TaoBR.Parab.PartE

open TaoBR.Parab Filter
open scoped Topology Pointwise

/-! ## Polar coordinates (copied from `restr_sparse_of_restr_uniform/Basic.lean`) -/

instance sphere_finite (n : ℕ) : IsFiniteMeasure (sphereMeasure n) := by
  unfold sphereMeasure; infer_instance

lemma nontrivial_E {n : ℕ} (hn : 1 ≤ n) : Nontrivial (E n) := by
  have : 0 < Module.finrank ℝ (E n) := by rw [finrank_euclideanSpace_fin]; omega
  exact Module.nontrivial_of_finrank_pos this

lemma polar_prod_lintegral {n : ℕ} (hn : 1 ≤ n) (F : E n → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ p : sphere (0 : E n) 1 × Ioi (0 : ℝ), F ((p.2 : ℝ) • (p.1 : E n))
      ∂((sphereMeasure n).prod (Measure.volumeIoiPow (n - 1))) := by
  have := nontrivial_E hn
  have h1 : ∫⁻ x, F x = ∫⁻ x : ({(0 : E n)}ᶜ : Set (E n)), F x
      ∂((volume : Measure (E n)).comap Subtype.val) := by
    rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
  have h2 := MeasurePreserving.symm (homeomorphUnitSphereProd (E n)).toMeasurableEquiv
    ((volume : Measure (E n)).measurePreserving_homeomorphUnitSphereProd)
  rw [h1, ← h2.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp only [finrank_euclideanSpace_fin]
  rfl

lemma polar_lintegral {n : ℕ} (hn : 1 ≤ n) (F : E n → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) * F (r • (ω : E n)))
      ∂(sphereMeasure n) := by
  rw [polar_prod_lintegral hn F hF, lintegral_prod]
  · congr 1; ext ω
    rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul]
    · exact lintegral_subtype_comap (μ := volume) measurableSet_Ioi
        (fun r : ℝ => ENNReal.ofReal (r ^ (n - 1)) * F (r • (ω : E n)))
    · exact (measurable_subtype_coe.pow_const _).ennreal_ofReal
    · exact hF.comp (by fun_prop)
  · exact (hF.comp ((measurable_subtype_coe.comp measurable_snd).smul
      (measurable_subtype_coe.comp measurable_fst))).aemeasurable

/-! ## Dilations (copied from `restr_sparse_of_restr_uniform/Est2.lean`) -/

/-- The affine map `y ↦ r⁻¹ • y + c`. -/
noncomputable def affE {n : ℕ} (r : ℝ) (c : E n) (y : E n) : E n := r⁻¹ • y + c

lemma affE_temperate {n : ℕ} (r : ℝ) (c : E n) : (affE r c).HasTemperateGrowth := by
  have h1 : (fun y : E n => r⁻¹ • y).HasTemperateGrowth :=
    (r⁻¹ • ContinuousLinearMap.id ℝ (E n)).hasTemperateGrowth
  exact h1.add (Function.HasTemperateGrowth.const c)

lemma affE_upper {n : ℕ} {r : ℝ} (hr : 0 < r) (c : E n) :
    ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖affE r c x‖) ^ k := by
  refine ⟨1, r * (1 + ‖c‖), fun x => ?_⟩
  have hx : x = r • (affE r c x - c) := by
    simp only [affE, add_sub_cancel_right, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have h2 : ‖x‖ ≤ r * (‖affE r c x‖ + ‖c‖) := by
    conv_lhs => rw [hx]
    rw [norm_smul, Real.norm_of_nonneg hr.le]
    gcongr
    exact norm_sub_le _ _
  calc ‖x‖ ≤ r * (‖affE r c x‖ + ‖c‖) := h2
    _ ≤ r * (1 + ‖c‖) * (1 + ‖affE r c x‖) ^ 1 := by
      rw [pow_one]
      have := mul_nonneg hr.le (mul_nonneg (norm_nonneg (affE r c x)) (norm_nonneg c))
      nlinarith

/-- `h ∘ affE r c` as a Schwartz map. -/
noncomputable def hAff {n : ℕ} (h : 𝓢(E n, ℂ)) {r : ℝ} (hr : 0 < r) (c : E n) : 𝓢(E n, ℂ) :=
  SchwartzMap.compCLM ℂ (affE_temperate r c) (affE_upper hr c) h

lemma fourier_hAff {n : ℕ} (h : E n → ℂ) {r : ℝ} (hr : 0 < r) (c ω : E n) :
    ‖𝓕 (fun y => h (r⁻¹ • y + c)) ω‖ = r ^ n * ‖𝓕 h (r • ω)‖ := by
  set G : E n → ℂ := fun x => 𝐞 (-⟪r • (x - c), ω⟫) • h x with hG
  have h1 : 𝓕 (fun y => h (r⁻¹ • y + c)) ω = ∫ y, G (r⁻¹ • y + c) := by
    rw [Real.fourier_eq]
    congr 1; ext y
    simp only [hG, add_sub_cancel_right, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have h2 : ∫ y, G (r⁻¹ • y + c) = r ^ n • ∫ x, G x := by
    rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun x => G (x + c)) hr.le,
      integral_add_right_eq_self (fun x => G x) c, finrank_euclideanSpace_fin]
  have h3 : ∫ x, G x = 𝐞 (⟪r • c, ω⟫) • 𝓕 h (r • ω) := by
    rw [Real.fourier_eq, Circle.smul_def, smul_eq_mul, ← integral_const_mul]
    congr 1; ext x
    have e : -⟪r • (x - c), ω⟫ = ⟪r • c, ω⟫ + -⟪x, r • ω⟫ := by
      simp only [inner_smul_left, inner_smul_right, inner_sub_left, RCLike.conj_to_real]; ring
    simp only [hG, Circle.smul_def, smul_eq_mul, e, AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]
  rw [h1, h2, h3, norm_smul, Circle.norm_smul (𝐞 _) , Real.norm_of_nonneg (by positivity)]

lemma lint_scale {n : ℕ} (F : E n → ℝ≥0∞) (hF : Measurable F) {r : ℝ} (hr : 0 < r) (c : E n) :
    ∫⁻ y, F (r⁻¹ • y + c) = ENNReal.ofReal (r ^ n) * ∫⁻ x, F x := by
  have hm : Measurable (fun y : E n => r⁻¹ • y) := measurable_const_smul _
  have hF' : Measurable (fun x : E n => F (x + c)) := hF.comp (measurable_add_const c)
  have := lintegral_map hF' hm (μ := (volume : Measure (E n)))
  rw [Measure.map_addHaar_smul volume (inv_ne_zero hr.ne'), lintegral_smul_measure,
    lintegral_add_right_eq_self F c, finrank_euclideanSpace_fin] at this
  rw [← this, inv_pow, inv_inv, abs_of_pos (by positivity), smul_eq_mul]

lemma tsupport_hAff {n : ℕ} (h : 𝓢(E n, ℂ)) {r : ℝ} (hr : 0 < r) {c : E n} {R : ℝ}
    (hsupp : tsupport h ⊆ closedBall c R) :
    tsupport (hAff h hr c) ⊆ closedBall 0 (r * R) := by
  have hcont : Continuous (affE (n := n) r c) := by unfold affE; fun_prop
  have hcl : IsClosed (affE r c ⁻¹' tsupport h) := (isClosed_tsupport _).preimage hcont
  have h1 : tsupport (hAff h hr c) ⊆ affE r c ⁻¹' tsupport h := by
    refine closure_minimal (fun y hy => ?_) hcl
    exact subset_tsupport _ hy
  refine h1.trans (fun y hy => ?_)
  have := hsupp hy
  rw [mem_closedBall, dist_eq_norm, affE, add_sub_cancel_right, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] at this
  rw [mem_closedBall, dist_zero_right]
  have := mul_le_mul_of_nonneg_left this hr.le
  rwa [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at this

lemma lp_pow {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ℝ} (hq : 1 ≤ q)
    (f : α → ℂ) :
    eLpNorm f (ENNReal.ofReal q) μ ^ q = ∫⁻ x, ‖f x‖ₑ ^ q ∂μ := by
  have hq0 : (0 : ℝ) < q := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne',
    ENNReal.rpow_one]

lemma per_r (n : ℕ) {q : ℝ} (hq : 1 ≤ q) {α : ℝ} (Cr : ℝ≥0)
    (hCr : ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ closedBall 0 R →
      eLpNorm (restriction f) (ENNReal.ofReal q) (sphereMeasure n) ≤
        Cr * ENNReal.ofReal (R ^ α) *
          eLpNorm f (ENNReal.ofReal q) (volume.restrict (closedBall 0 R)))
    {R : ℝ} (hR : 1 ≤ R) (c : E n) (h : 𝓢(E n, ℂ)) (hsupp : tsupport h ⊆ closedBall c R)
    {r : ℝ} (hr1 : 1 / 2 < r) (hr2 : r ≤ 2) :
    ∫⁻ ω, ‖𝓕 (h : E n → ℂ) (r • (ω : E n))‖ₑ ^ q ∂(sphereMeasure n) ≤
      ENNReal.ofReal (2 ^ ((n : ℝ) * q)) *
        ((Cr * ENNReal.ofReal ((2 * R) ^ α)) ^ q * ∫⁻ y, ‖h y‖ₑ ^ q) := by
  have hr : 0 < r := by linarith
  have hq0 : (0 : ℝ) ≤ q := by linarith
  set g := hAff h hr c
  have hg : tsupport g ⊆ closedBall 0 (2 * R) :=
    (tsupport_hAff h hr hsupp).trans (closedBall_subset_closedBall (by nlinarith))
  have key := hCr (2 * R) (by linarith) g hg
  have key2 := ENNReal.rpow_le_rpow key hq0
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq0, lp_pow hq, lp_pow hq] at key2
  -- left side
  have hA : ∫⁻ ω, ‖restriction (g : E n → ℂ) ω‖ₑ ^ q ∂(sphereMeasure n) =
      ENNReal.ofReal (r ^ n) ^ q *
        ∫⁻ ω, ‖𝓕 (h : E n → ℂ) (r • (ω : E n))‖ₑ ^ q ∂(sphereMeasure n) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0 ENNReal.ofReal_ne_top)]
    congr 1; ext ω
    have e := fourier_hAff (h : E n → ℂ) hr c (ω : E n)
    have : ‖restriction (g : E n → ℂ) ω‖ₑ = ENNReal.ofReal (r ^ n) * ‖𝓕 (h : E n → ℂ) (r • (ω : E n))‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
      exact congrArg ENNReal.ofReal e
    rw [this, ENNReal.mul_rpow_of_nonneg _ _ hq0]
  -- right side
  have hB : ∫⁻ y, ‖g y‖ₑ ^ q ∂(volume.restrict (closedBall 0 (2 * R))) ≤
      ENNReal.ofReal (r ^ n) * ∫⁻ y, ‖h y‖ₑ ^ q := by
    refine (lintegral_mono' Measure.restrict_le_self le_rfl).trans (le_of_eq ?_)
    exact lint_scale (fun x => ‖h x‖ₑ ^ q)
      (h.continuous.measurable.enorm.pow_const q) hr c
  rw [hA] at key2
  have key3 := key2.trans (mul_le_mul' le_rfl hB)
  set X := ∫⁻ ω, ‖𝓕 (h : E n → ℂ) (r • (ω : E n))‖ₑ ^ q ∂(sphereMeasure n)
  set H := ∫⁻ y, ‖h y‖ₑ ^ q
  set K := (Cr * ENNReal.ofReal ((2 * R) ^ α)) ^ q
  have hrn0 : ENNReal.ofReal (r ^ n) ^ q ≠ 0 := by
    have : 0 < r ^ n := by positivity
    exact (ENNReal.rpow_pos (by simpa using this) (by simp)).ne'
  have hrnT : ENNReal.ofReal (r ^ n) ^ q ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hq0 (by simp)
  have hreal : r ^ n ≤ (r ^ n) ^ q * 2 ^ ((n : ℝ) * q) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast, ← Real.mul_rpow (by positivity)
      (by positivity), ← mul_pow]
    have h1 : 1 ≤ (r * 2) ^ n := one_le_pow₀ (by linarith)
    calc r ^ n ≤ (r * 2) ^ n := pow_le_pow_left₀ hr.le (by linarith) n
      _ ≤ ((r * 2) ^ n) ^ q := Real.self_le_rpow_of_one_le h1 hq
  have hE : ENNReal.ofReal (r ^ n) ≤ ENNReal.ofReal (r ^ n) ^ q * ENNReal.ofReal (2 ^ ((n : ℝ) * q)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  refine (ENNReal.mul_le_mul_iff_right hrn0 hrnT).mp ?_
  calc ENNReal.ofReal (r ^ n) ^ q * X ≤ K * (ENNReal.ofReal (r ^ n) * H) := key3
    _ ≤ K * (ENNReal.ofReal (r ^ n) ^ q * ENNReal.ofReal (2 ^ ((n : ℝ) * q)) * H) := by gcongr
    _ = _ := by ring

/-! ## `annulus_of_restr` -/

/-- **T1 (annulus estimate from spherical `R(p, 0)`).** -/
theorem annulus_of_restr {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p)
    (h : Restr n (ENNReal.ofReal p) 0) :
    ∃ C : ℝ≥0, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ f : 𝓢(E n, ℂ), HasCompactSupport (f : E n → ℂ) →
      ∫⁻ ξ in {ξ : E n | |‖ξ‖ - 1| < δ}, ‖𝓕 (f : E n → ℂ) ξ‖ₑ ^ p ≤
        C * ENNReal.ofReal δ * ∫⁻ y, ‖f y‖ₑ ^ p := by
  obtain ⟨Cr, hCr⟩ := h
  have hn1 : 1 ≤ n := by omega
  have hq0 : (0 : ℝ) ≤ p := by linarith
  refine ⟨Real.toNNReal ((3 / 2) ^ (n - 1) * 2 * 2 ^ ((n : ℝ) * p)) * Cr ^ p, ?_⟩
  intro δ hδ0 hδ f hf
  obtain ⟨R0, hR0⟩ := (IsCompact.isBounded hf).subset_closedBall (0 : E n)
  set R := max R0 1
  have hR : 1 ≤ R := le_max_right _ _
  have hsupp : tsupport f ⊆ closedBall 0 R :=
    hR0.trans (closedBall_subset_closedBall (le_max_left _ _))
  set A : Set (E n) := {ξ : E n | |‖ξ‖ - 1| < δ}
  set F : E n → ℝ≥0∞ := fun η => ‖𝓕 (f : E n → ℂ) η‖ₑ ^ p with hFdef
  have hFc : Continuous (𝓕 (f : E n → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 f).continuous
  have hFm : Measurable F := hFc.measurable.enorm.pow_const p
  have hA : MeasurableSet A :=
    measurableSet_lt ((measurable_norm.sub measurable_const).abs) measurable_const
  set H := ∫⁻ y, ‖f y‖ₑ ^ p
  set C : ℝ≥0∞ := ENNReal.ofReal ((3 / 2) ^ (n - 1))
  set M : ℝ≥0∞ := ENNReal.ofReal (2 ^ ((n : ℝ) * p)) * ((Cr : ℝ≥0∞) ^ p * H)
  set I : Set ℝ := Ioo (1 - δ) (1 + δ)
  have step1 : ∫⁻ η in A, F η ≤ ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ),
      I.indicator (fun r => C * F (r • (ω : E n))) r) ∂(sphereMeasure n) := by
    rw [← lintegral_indicator hA, polar_lintegral hn1 _ (hFm.indicator hA)]
    refine lintegral_mono fun ω => setLIntegral_mono' measurableSet_Ioi fun r hr => ?_
    have hr0 : (0 : ℝ) < r := hr
    by_cases hm : r • (ω : E n) ∈ A
    · have hnorm : ‖r • (ω : E n)‖ = r := by
        rw [norm_smul, Real.norm_of_nonneg hr0.le]; simp
      have hI : r ∈ I := by
        have h' : |r - 1| < δ := by simpa [A, hnorm] using hm
        rw [abs_sub_lt_iff] at h'
        exact ⟨by linarith, by linarith⟩
      rw [indicator_of_mem hm, indicator_of_mem hI]
      gcongr
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hr0.le (by linarith [hI.2]) _)
    · rw [indicator_of_notMem hm, mul_zero]; exact bot_le
  have hmeas : Measurable (Function.uncurry fun (ω : sphere (0 : E n) 1) (r : ℝ) =>
      I.indicator (fun r => C * F (r • (ω : E n))) r) := by
    have e : (Function.uncurry fun (ω : sphere (0 : E n) 1) (r : ℝ) =>
        I.indicator (fun r => C * F (r • (ω : E n))) r) =
        (Prod.snd ⁻¹' I).indicator
          (fun p : sphere (0 : E n) 1 × ℝ => C * F (p.2 • (p.1 : E n))) := by
      ext p; simp [Function.uncurry, indicator]
    rw [e]
    refine Measurable.indicator ?_ (measurable_snd measurableSet_Ioo)
    exact measurable_const.mul (hFm.comp (measurable_snd.smul
      (measurable_subtype_coe.comp measurable_fst)))
  have step2 := lintegral_lintegral_swap (μ := sphereMeasure n)
    (ν := volume.restrict (Ioi (0 : ℝ))) hmeas.aemeasurable
  rw [step2] at step1
  have step3 : ∫⁻ r in Ioi (0 : ℝ), (∫⁻ ω, I.indicator (fun r => C * F (r • (ω : E n))) r
      ∂(sphereMeasure n)) ≤ ∫⁻ r, I.indicator (fun _ => C * M) r := by
    refine (lintegral_mono fun r => ?_).trans (setLIntegral_le_lintegral _ _)
    by_cases hI : r ∈ I
    · simp only [indicator_of_mem hI]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      have := per_r n hp (α := 0) Cr hCr hR 0 f hsupp (r := r) (by linarith [hI.1])
        (by linarith [hI.2])
      simpa [M, Real.rpow_zero] using this
    · simp [indicator_of_notMem hI]
  rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo] at step3
  refine step1.trans (step3.trans (le_of_eq ?_))
  have h2δ : ENNReal.ofReal (1 + δ - (1 - δ)) = ENNReal.ofReal 2 * ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
  have hC2 : ((Real.toNNReal ((3 / 2) ^ (n - 1) * 2 * 2 ^ ((n : ℝ) * p)) * Cr ^ p : ℝ≥0) :
      ℝ≥0∞) = C * ENNReal.ofReal 2 * ENNReal.ofReal (2 ^ ((n : ℝ) * p)) *
        (Cr : ℝ≥0∞) ^ p := by
    rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ hq0]
    change ENNReal.ofReal _ * _ = _
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  rw [hC2, h2δ]
  simp only [M]
  ring

/-! ## `map_anisoLin` -/

/-- The diagonal of `anisoLin λ`. -/
noncomputable def dvec (m : ℕ) (lam : ℝ) : Fin (m + 1) → ℝ := Fin.snoc (fun _ => lam) (lam ^ 2)

/-- `anisoLin λ` as a linear map. -/
noncomputable def anisoL (m : ℕ) (lam : ℝ) : E (m + 1) →ₗ[ℝ] E (m + 1) :=
  Matrix.toLpLin 2 2 (Matrix.diagonal (dvec m lam))

lemma anisoL_apply (m : ℕ) (lam : ℝ) (x : E (m + 1)) : anisoL m lam x = anisoLin lam x := by
  ext i
  simp only [anisoL, Matrix.toLpLin_apply, Matrix.mulVec_diagonal, anisoLin, mkPoint, horiz, vert,
    PiLp.toLp_apply, PiLp.smul_apply]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [dvec]
  · simp [dvec]

lemma det_anisoL (m : ℕ) (lam : ℝ) : LinearMap.det (anisoL m lam) = lam ^ (m + 2) := by
  rw [anisoL, Matrix.toLpLin_eq_toLin, LinearMap.det_toLin, Matrix.det_diagonal,
    Fin.prod_univ_castSucc]
  simp [dvec]
  ring

/-- **T2a (Jacobian of the anisotropic dilation).** -/
theorem map_anisoLin (m : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    (volume : Measure (E (m + 1))).map (anisoLin lam) =
      ENNReal.ofReal ((lam ^ (m + 2))⁻¹) • volume := by
  have hfun : (anisoLin lam : E (m + 1) → E (m + 1)) = anisoL m lam := by
    funext x; exact (anisoL_apply m lam x).symm
  have hdet : LinearMap.det (anisoL m lam) ≠ 0 := by
    rw [det_anisoL]; positivity
  rw [hfun, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, det_anisoL,
    abs_of_pos (by positivity)]

end TaoBR.Parab.PartE

end S_PartE

namespace TaoBR.Parab
alias annulus_of_restr := TaoBR.Parab.PartE.annulus_of_restr
alias map_anisoLin := TaoBR.Parab.PartE.map_anisoLin
end TaoBR.Parab

section S_PartF

/-! # Part F: `exists_aniso_rescale` and `thick_of_annulus` (parabolic rescaling) -/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace


namespace TaoBR.Parab.PartF

open TaoBR.Parab Filter Complex
open scoped Topology Real

/-! ## Coordinates -/

section Coords

variable {m : ℕ}

@[simp] theorem mkPoint_castSucc (u : E m) (t : ℝ) (i : Fin m) :
    mkPoint u t (Fin.castSucc i) = u i := by
  simp [mkPoint]

@[simp] theorem mkPoint_last (u : E m) (t : ℝ) : mkPoint u t (Fin.last m) = t := by
  simp [mkPoint]

@[simp] theorem horiz_apply (y : E (m + 1)) (i : Fin m) : horiz y i = y (Fin.castSucc i) := by
  simp [horiz]

@[simp] theorem horiz_mkPoint (u : E m) (t : ℝ) : horiz (mkPoint u t) = u := by
  ext i; simp

@[simp] theorem vert_mkPoint (u : E m) (t : ℝ) : vert (mkPoint u t) = t := by
  simp [vert]

theorem mkPoint_horiz_vert (ξ : E (m + 1)) : mkPoint (horiz ξ) (vert ξ) = ξ := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [vert]
  | cast j => simp

theorem mkPoint_sub (u u' : E m) (t t' : ℝ) :
    mkPoint u t - mkPoint u' t' = mkPoint (u - u') (t - t') := by
  ext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

theorem norm_mkPoint_sq (u : E m) (t : ℝ) : ‖mkPoint u t‖ ^ 2 = ‖u‖ ^ 2 + t ^ 2 := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), Fin.sum_univ_castSucc]
  simp

theorem anisoLin_apply_castSucc (lam : ℝ) (η : E (m + 1)) (j : Fin m) :
    anisoLin lam η (Fin.castSucc j) = lam * η (Fin.castSucc j) := by
  simp [anisoLin]

theorem anisoLin_apply_last (lam : ℝ) (η : E (m + 1)) :
    anisoLin lam η (Fin.last m) = lam ^ 2 * η (Fin.last m) := by
  simp [anisoLin, vert]

theorem anisoLin_add (lam : ℝ) (x y : E (m + 1)) :
    anisoLin lam (x + y) = anisoLin lam x + anisoLin lam y := by
  ext i
  induction i using Fin.lastCases with
  | last => simp only [anisoLin_apply_last, PiLp.add_apply]; ring
  | cast j => simp only [anisoLin_apply_castSucc, PiLp.add_apply]; ring

theorem anisoLin_smul (lam c : ℝ) (x : E (m + 1)) :
    anisoLin lam (c • x) = c • anisoLin lam x := by
  ext i
  induction i using Fin.lastCases with
  | last => simp only [anisoLin_apply_last, PiLp.smul_apply, smul_eq_mul]; ring
  | cast j => simp only [anisoLin_apply_castSucc, PiLp.smul_apply, smul_eq_mul]; ring

theorem anisoLin_inv {lam : ℝ} (hlam : lam ≠ 0) (x : E (m + 1)) :
    anisoLin lam⁻¹ (anisoLin lam x) = x := by
  ext i
  induction i using Fin.lastCases with
  | last => simp only [anisoLin_apply_last]; field_simp
  | cast j => simp only [anisoLin_apply_castSucc]; field_simp

/-- `anisoLin λ` as a linear equivalence. -/
noncomputable def anisoLE {lam : ℝ} (hlam : lam ≠ 0) : E (m + 1) ≃ₗ[ℝ] E (m + 1) where
  toFun := anisoLin lam
  invFun := anisoLin lam⁻¹
  map_add' := anisoLin_add lam
  map_smul' := anisoLin_smul lam
  left_inv := anisoLin_inv hlam
  right_inv x := by
    have := anisoLin_inv (inv_ne_zero hlam) x
    rwa [inv_inv] at this

/-- `anisoLin λ` as a continuous linear equivalence. -/
noncomputable def anisoCLE {lam : ℝ} (hlam : lam ≠ 0) : E (m + 1) ≃L[ℝ] E (m + 1) :=
  (anisoLE hlam).toContinuousLinearEquiv

@[simp] theorem anisoCLE_apply {lam : ℝ} (hlam : lam ≠ 0) (x : E (m + 1)) :
    anisoCLE hlam x = anisoLin lam x := rfl

theorem inner_anisoLin (lam : ℝ) (x η : E (m + 1)) :
    ⟪x, anisoLin lam η⟫ = ⟪anisoLin lam x, η⟫ := by
  simp only [PiLp.inner_apply, Fin.sum_univ_castSucc, anisoLin_apply_castSucc,
    anisoLin_apply_last]
  simp only [RCLike.inner_apply, conj_trivial]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => by ring
  · ring

theorem inner_mkPoint_zero_one (x : E (m + 1)) : ⟪x, mkPoint 0 1⟫ = vert x := by
  simp only [PiLp.inner_apply, Fin.sum_univ_castSucc, mkPoint_castSucc, mkPoint_last]
  simp [vert]

end Coords

/-! ## The rescaled function -/

section Rescale

variable {m : ℕ}

theorem contDiff_vertChar : ContDiff ℝ (⊤ : ℕ∞) fun x : E (m + 1) => ((𝐞 (-vert x) : Circle) : ℂ) := by
  simp only [Real.fourierChar_apply]
  have hv : ContDiff ℝ (⊤ : ℕ∞) fun x : E (m + 1) => vert x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).contDiff
  apply Complex.contDiff_exp.comp
  apply ContDiff.mul _ contDiff_const
  exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hv.neg)

theorem enorm_circle (z : Circle) : ‖(z : ℂ)‖ₑ = 1 := by
  rw [← ofReal_norm, Circle.norm_coe, ENNReal.ofReal_one]

/-- **T2b (the rescaled function).** Verbatim restatement of the Blueprint's
`exists_aniso_rescale`. -/
theorem exists_aniso_rescale (m : ℕ) {lam : ℝ} (hlam : 0 < lam) (g : 𝓢(E (m + 1), ℂ))
    (hg : HasCompactSupport (g : E (m + 1) → ℂ)) :
    ∃ f : 𝓢(E (m + 1), ℂ), HasCompactSupport (f : E (m + 1) → ℂ) ∧
      (∀ η : E (m + 1), 𝓕 (f : E (m + 1) → ℂ) (anisoMap lam η) =
        (((lam ^ (m + 2))⁻¹ : ℝ) : ℂ) * 𝓕 (g : E (m + 1) → ℂ) η) ∧
      ∀ p : ℝ, 0 < p →
        ∫⁻ y, ‖f y‖ₑ ^ p = ENNReal.ofReal ((lam ^ (m + 2))⁻¹) * ∫⁻ y, ‖g y‖ₑ ^ p := by
  set A := anisoCLE (m := m) hlam.ne' with hA
  have hme : MeasurableEmbedding (anisoLin (m := m) lam) :=
    A.toHomeomorph.measurableEmbedding
  have hmap := map_anisoLin m hlam
  set F : E (m + 1) → ℂ := fun x => g (anisoLin lam x) * ((𝐞 (-vert x) : Circle) : ℂ) with hF
  have hc : HasCompactSupport F := by
    have h1 : HasCompactSupport (fun x => g (anisoLin lam x)) :=
      hg.comp_homeomorph A.toHomeomorph
    exact h1.mul_right
  have hcd : ContDiff ℝ (⊤ : ℕ∞) F :=
    ((g.smooth ⊤).comp A.contDiff).mul contDiff_vertChar
  refine ⟨hc.toSchwartzMap hcd, hc, fun η => ?_, fun p _ => ?_⟩
  · change 𝓕 F (anisoMap lam η) = _
    rw [Real.fourier_eq, Real.fourier_eq]
    have e : ∀ x : E (m + 1), 𝐞 (-⟪x, anisoMap lam η⟫) • F x =
        (fun y => 𝐞 (-⟪y, η⟫) • g y) (anisoLin lam x) := by
      intro x
      simp only [hF, anisoMap, inner_sub_right, inner_anisoLin, inner_mkPoint_zero_one,
        Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
      rw [mul_left_comm, ← Complex.exp_add, mul_comm]
      congr 2
      push_cast; ring
    simp_rw [e]
    have h1 := hme.integral_map (μ := volume) (fun y => 𝐞 (-⟪y, η⟫) • g y)
    rw [← h1, hmap, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
      Complex.real_smul]
  · change ∫⁻ y, ‖F y‖ₑ ^ p = _
    simp only [hF, enorm_mul, enorm_circle, mul_one]
    rw [← hme.lintegral_map (fun y => ‖g y‖ₑ ^ p), hmap, lintegral_smul_measure, smul_eq_mul]

end Rescale

/-! ## Geometry: the rescaled thickening lies in a thin annulus -/

section Geom

variable {m : ℕ}

theorem anisoMap_eq (lam : ℝ) (η : E (m + 1)) :
    anisoMap lam η = mkPoint (lam • horiz η) (lam ^ 2 * vert η - 1) := by
  rw [anisoMap, anisoLin, mkPoint_sub, sub_zero]

/-- Real-variable core of the geometry. -/
theorem annulus_core {ρ a b t : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 16) (hb0 : 0 ≤ b)
    (hb : b ≤ 5 / 4) (hd : |a - b| < ρ) (hs : |t - b ^ 2 / 2| < ρ) :
    |(ρ * a ^ 2 + (ρ * t - 1) ^ 2) - 1| ≤ 6 * ρ ^ 2 := by
  set d := a - b with hd_def
  set s := t - b ^ 2 / 2 with hs_def
  have ha : a = b + d := by rw [hd_def]; ring
  have ht : t = b ^ 2 / 2 + s := by rw [hs_def]; ring
  have hX : (ρ * a ^ 2 + (ρ * t - 1) ^ 2) - 1 = ρ * (d * (2 * b + d) - 2 * s) + ρ ^ 2 * t ^ 2 := by
    rw [ha, ht]; ring
  have h2 : |2 * b + d| ≤ 3 := by
    rw [abs_lt] at hd; rw [abs_le]; constructor <;> linarith
  have h1 : |d * (2 * b + d)| ≤ 3 * ρ := by
    rw [abs_mul]
    calc |d| * |2 * b + d| ≤ ρ * 3 := mul_le_mul hd.le h2 (abs_nonneg _) hρ.le
      _ = 3 * ρ := by ring
  have h3 : |d * (2 * b + d) - 2 * s| ≤ 5 * ρ := by
    calc |d * (2 * b + d) - 2 * s| ≤ |d * (2 * b + d)| + |2 * s| := abs_sub _ _
      _ ≤ 3 * ρ + 2 * ρ := by
          have : |2 * s| = 2 * |s| := by rw [abs_mul, abs_two]
          linarith
      _ = 5 * ρ := by ring
  have ht1 : t ^ 2 ≤ 1 := by
    rw [abs_lt] at hs
    have : b ^ 2 ≤ 25 / 16 := by nlinarith
    rw [sq_le_one_iff_abs_le_one, abs_le]; constructor <;> nlinarith
  rw [hX]
  calc |ρ * (d * (2 * b + d) - 2 * s) + ρ ^ 2 * t ^ 2|
      ≤ |ρ * (d * (2 * b + d) - 2 * s)| + |ρ ^ 2 * t ^ 2| := abs_add_le _ _
    _ ≤ ρ * (5 * ρ) + ρ ^ 2 * 1 := by
        rw [abs_mul ρ, abs_of_pos hρ, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ρ ^ 2 * t ^ 2)]
        gcongr
    _ = 6 * ρ ^ 2 := by ring

theorem anisoMap_mem_annulus {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 16) {η : E (m + 1)}
    (hη : η ∈ thickening ρ (parabSet m)) :
    |‖anisoMap (Real.sqrt ρ) η‖ - 1| < 16 * ρ ^ 2 := by
  obtain ⟨z, ⟨u, hu, rfl⟩, hdist⟩ := mem_thickening_iff.1 hη
  rw [mem_closedBall_zero_iff] at hu
  set v := horiz η
  set t := vert η
  have hsub : η - graphPt u = mkPoint (v - u) (t - ‖u‖ ^ 2 / 2) := by
    conv_lhs => rw [← mkPoint_horiz_vert η]
    rw [graphPt, mkPoint_sub]
  rw [dist_eq_norm, hsub] at hdist
  have hsq : ‖v - u‖ ^ 2 + (t - ‖u‖ ^ 2 / 2) ^ 2 < ρ ^ 2 := by
    rw [← norm_mkPoint_sq]
    exact pow_lt_pow_left₀ hdist (norm_nonneg _) two_ne_zero
  have hvu : ‖v - u‖ < ρ := by nlinarith [norm_nonneg (v - u)]
  have hs : |t - ‖u‖ ^ 2 / 2| < ρ :=
    abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg ‖v - u‖]) hρ.le
  have hsq2 : ‖anisoMap (Real.sqrt ρ) η‖ ^ 2 = ρ * ‖v‖ ^ 2 + (ρ * t - 1) ^ 2 := by
    rw [anisoMap_eq, norm_mkPoint_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt hρ.le]
  have hcore := annulus_core hρ hρ1 (norm_nonneg u) hu
    (lt_of_le_of_lt (abs_norm_sub_norm_le v u) hvu) hs
  rw [← hsq2] at hcore
  set A := ‖anisoMap (Real.sqrt ρ) η‖
  have hA0 : 0 ≤ A := norm_nonneg _
  calc |A - 1| ≤ |A - 1| * (A + 1) := le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    _ = |A ^ 2 - 1| := by
        rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ A + 1), ← abs_mul]; ring_nf
    _ ≤ 6 * ρ ^ 2 := hcore
    _ < 16 * ρ ^ 2 := by nlinarith

end Geom

/-! ## Exponent bookkeeping -/

theorem exponent_identity (m : ℕ) {p R : ℝ} (hp : 0 < p) (hR : 0 < R) :
    ((Real.sqrt (1 / (16 * R))) ^ (m + 2)) ^ p * ((Real.sqrt (1 / (16 * R))) ^ (m + 2))⁻¹ *
        (16 * (1 / (16 * R)) ^ 2) * ((Real.sqrt (1 / (16 * R))) ^ (m + 2))⁻¹ =
      16 * 16 ^ (p * alphaPar m p - 1) * (R ^ alphaPar m p) ^ p * (1 / R) := by
  set ρ := 1 / (16 * R) with hρ_def
  have hρ : 0 < ρ := by positivity
  have hK : (Real.sqrt ρ) ^ (m + 2) = ρ ^ (((m : ℝ) + 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    congr 1; push_cast; ring
  set c : ℝ := ((m : ℝ) + 2) / 2
  have h1 : (ρ ^ c) ^ p = ρ ^ (c * p) := (Real.rpow_mul hρ.le _ _).symm
  have h2 : (ρ ^ c)⁻¹ = ρ ^ (-c) := (Real.rpow_neg hρ.le _).symm
  have h3 : ρ ^ 2 = ρ ^ (2 : ℝ) := (Real.rpow_two ρ).symm
  have hL : ρ ^ (c * p) * ρ ^ (-c) * (16 * ρ ^ (2 : ℝ)) * ρ ^ (-c) =
      16 * ρ ^ (c * p + -c + 2 + -c) := by
    rw [Real.rpow_add hρ, Real.rpow_add hρ, Real.rpow_add hρ]; ring
  set a := alphaPar m p with ha
  have hRr : 16 * 16 ^ (p * a - 1) * (R ^ a) ^ p * (1 / R) = 16 * (16 * R) ^ (p * a - 1) := by
    rw [← Real.rpow_mul hR.le, one_div R, ← Real.rpow_neg_one R,
      Real.mul_rpow (by norm_num) hR.le, Real.rpow_sub hR, Real.rpow_neg_one,
      mul_comm a p, Real.rpow_one]
    field_simp
  rw [hK, h1, h2, h3, hL, hRr, hρ_def, one_div, Real.inv_rpow (by positivity),
    ← Real.rpow_neg (by positivity)]
  congr 2
  rw [ha]; unfold alphaPar
  field_simp
  ring

/-! ## The thickened parabolic estimate -/

/-- **T2c (thickened parabolic estimate).** Verbatim restatement of the Blueprint's
`thick_of_annulus`. -/
theorem thick_of_annulus (m : ℕ) {p : ℝ} (hp : 1 ≤ p)
    (hA : ∃ C : ℝ≥0, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ f : 𝓢(E (m + 1), ℂ),
      HasCompactSupport (f : E (m + 1) → ℂ) →
        ∫⁻ ξ in {ξ : E (m + 1) | |‖ξ‖ - 1| < δ}, ‖𝓕 (f : E (m + 1) → ℂ) ξ‖ₑ ^ p ≤
          C * ENNReal.ofReal δ * ∫⁻ y, ‖f y‖ₑ ^ p) :
    ThickRestr (parabSet m) p (alphaPar m p) := by
  obtain ⟨C, hC⟩ := hA
  have hp0 : 0 < p := by linarith
  refine ⟨C * Real.toNNReal (16 * 16 ^ (p * alphaPar m p - 1)), fun R hR g hg => ?_⟩
  have hR0 : 0 < R := by linarith
  set ρ := 1 / (16 * R) with hρ_def
  have hρ : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 / 16 := by
    rw [hρ_def, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set lam := Real.sqrt ρ with hlam_def
  have hlam : 0 < lam := Real.sqrt_pos.2 hρ
  set δ := 16 * ρ ^ 2 with hδ_def
  have hδ : 0 < δ := by positivity
  have hδ2 : δ ≤ 1 / 2 := by rw [hδ_def]; nlinarith
  have hgc : HasCompactSupport (g : E (m + 1) → ℂ) :=
    (isCompact_closedBall (0 : E (m + 1)) R).of_isClosed_subset (isClosed_tsupport _) hg
  obtain ⟨f, hfc, hfF, hfL⟩ := exists_aniso_rescale m hlam g hgc
  set K := lam ^ (m + 2) with hK_def
  have hK : 0 < K := by positivity
  set Ann : Set (E (m + 1)) := {ξ | |‖ξ‖ - 1| < δ} with hAnn_def
  have hAnn : MeasurableSet Ann := measurableSet_lt (by fun_prop) measurable_const
  set H : E (m + 1) → ℝ≥0∞ := Ann.indicator fun ξ => ‖𝓕 (f : E (m + 1) → ℂ) ξ‖ₑ ^ p with hH
  -- pointwise identity on the thickening
  have hpt : ∀ η ∈ thickening (1 / (16 * R)) (parabSet m),
      ‖𝓕 (g : E (m + 1) → ℂ) η‖ₑ ^ p = ENNReal.ofReal (K ^ p) * H (anisoMap lam η) := by
    intro η hη
    have e1 : 𝓕 (g : E (m + 1) → ℂ) η = (K : ℂ) * 𝓕 (f : E (m + 1) → ℂ) (anisoMap lam η) := by
      rw [hfF η, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hK.ne', Complex.ofReal_one,
        one_mul]
    have hmem : anisoMap lam η ∈ Ann := anisoMap_mem_annulus hρ hρ1 hη
    rw [hH, indicator_of_mem hmem, e1, enorm_mul, ← ofReal_norm, Complex.norm_real,
      Real.norm_of_nonneg hK.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      ENNReal.ofReal_rpow_of_nonneg hK.le hp0.le]
  -- change of variables
  have hme : MeasurableEmbedding (anisoLin (m := m) lam) :=
    (anisoCLE (m := m) hlam.ne').toHomeomorph.measurableEmbedding
  have hcov : ∫⁻ η, H (anisoMap lam η) =
      ENNReal.ofReal K⁻¹ * ∫⁻ ξ in Ann, ‖𝓕 (f : E (m + 1) → ℂ) ξ‖ₑ ^ p := by
    have h1 := hme.lintegral_map (μ := volume) (fun ξ => H (ξ - mkPoint 0 1))
    simp only [anisoMap]
    rw [← h1, map_anisoLin m hlam, lintegral_smul_measure, smul_eq_mul,
      lintegral_sub_right_eq_self H (mkPoint 0 1), hH, lintegral_indicator hAnn]
  have hfL' := hfL p hp0
  have hann := hC δ hδ hδ2 f hfc
  have key := exponent_identity m hp0 hR0
  calc ∫⁻ η in thickening (1 / (16 * R)) (parabSet m), ‖𝓕 (g : E (m + 1) → ℂ) η‖ₑ ^ p
      = ∫⁻ η in thickening (1 / (16 * R)) (parabSet m),
          ENNReal.ofReal (K ^ p) * H (anisoMap lam η) :=
        setLIntegral_congr_fun isOpen_thickening.measurableSet hpt
    _ ≤ ∫⁻ η, ENNReal.ofReal (K ^ p) * H (anisoMap lam η) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (K ^ p) * (ENNReal.ofReal K⁻¹ *
          ∫⁻ ξ in Ann, ‖𝓕 (f : E (m + 1) → ℂ) ξ‖ₑ ^ p) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hcov]
    _ ≤ ENNReal.ofReal (K ^ p) * (ENNReal.ofReal K⁻¹ *
          (C * ENNReal.ofReal δ * (ENNReal.ofReal K⁻¹ * ∫⁻ y, ‖g y‖ₑ ^ p))) := by
        rw [← hfL']; gcongr
    _ = C * (ENNReal.ofReal (K ^ p) * ENNReal.ofReal K⁻¹ * ENNReal.ofReal δ *
          ENNReal.ofReal K⁻¹) * ∫⁻ y, ‖g y‖ₑ ^ p := by ring
    _ = C * ENNReal.ofReal (K ^ p * K⁻¹ * δ * K⁻¹) * ∫⁻ y, ‖g y‖ₑ ^ p := by
        rw [ENNReal.ofReal_mul (show 0 ≤ K ^ p * K⁻¹ * δ by positivity),
          ENNReal.ofReal_mul (show 0 ≤ K ^ p * K⁻¹ by positivity),
          ENNReal.ofReal_mul (show 0 ≤ K ^ p by positivity)]
    _ = C * ENNReal.ofReal (16 * 16 ^ (p * alphaPar m p - 1) * (R ^ alphaPar m p) ^ p *
          (1 / R)) * ∫⁻ y, ‖g y‖ₑ ^ p := by
        rw [← key]
    _ = ↑(C * Real.toNNReal (16 * 16 ^ (p * alphaPar m p - 1))) *
          ENNReal.ofReal (R ^ alphaPar m p) ^ p * ENNReal.ofReal (1 / R) *
          ∫⁻ y, ‖g y‖ₑ ^ p := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, ENNReal.coe_mul]
        change _ = ↑C * ENNReal.ofReal (16 * 16 ^ (p * alphaPar m p - 1)) * _ * _ * _
        ring

end TaoBR.Parab.PartF

end S_PartF

namespace TaoBR.Parab
alias thick_of_annulus := TaoBR.Parab.PartF.thick_of_annulus
end TaoBR.Parab

section S_PartG

/-! # Part G: `parab_decay_vert` (vertical Fourier decay of the paraboloid measure) -/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace


namespace TaoBR.Parab.PartG

open TaoBR.Parab Filter Complex
open scoped Topology Real

/-! ## Coordinates (copied from `proofs/thm410/PartB1.lean`) -/

section Coords

variable {m : ℕ}

@[simp] theorem mkPoint_castSucc (u : E m) (t : ℝ) (i : Fin m) :
    mkPoint u t (Fin.castSucc i) = u i := by
  simp [mkPoint]

@[simp] theorem mkPoint_last (u : E m) (t : ℝ) : mkPoint u t (Fin.last m) = t := by
  simp [mkPoint]

@[simp] theorem horiz_apply (y : E (m + 1)) (i : Fin m) : horiz y i = y (Fin.castSucc i) := by
  simp [horiz]

theorem continuous_mkPoint : Continuous fun q : E m × ℝ => mkPoint q.1 q.2 := by
  unfold mkPoint
  apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp
  apply continuous_pi; intro i
  induction i using Fin.lastCases with
  | last => simp; fun_prop
  | cast j => simp; fun_prop

theorem continuous_graphPt : Continuous (graphPt : E m → E (m + 1)) :=
  continuous_mkPoint.comp (continuous_id.prodMk (by fun_prop))

theorem inner_graphPt (v : E m) (x : E (m + 1)) :
    ⟪graphPt v, x⟫ = ⟪v, horiz x⟫ + ‖v‖ ^ 2 / 2 * vert x := by
  simp only [graphPt, PiLp.inner_apply, Fin.sum_univ_castSucc, mkPoint_castSucc, mkPoint_last,
    horiz_apply, vert]
  simp [mul_comm]

end Coords

/-! ## The weight as a Schwartz map and Fourier inversion -/

variable {m : ℕ}

theorem hasCompactSupport_wC (m : ℕ) : HasCompactSupport fun v : E m => ((wt m v : ℝ) : ℂ) :=
  (wBump m).hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero

theorem contDiff_wC (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) fun v : E m => ((wt m v : ℝ) : ℂ) :=
  Complex.ofRealCLM.contDiff.comp (wBump m).contDiff

/-- `w` as a Schwartz map. -/
noncomputable def W (m : ℕ) : 𝓢(E m, ℂ) := (hasCompactSupport_wC m).toSchwartzMap (contDiff_wC m)

/-- `ŵ`. -/
noncomputable def Wh (m : ℕ) : 𝓢(E m, ℂ) := 𝓕 (W m)

theorem W_apply (v : E m) : W m v = ((wt m v : ℝ) : ℂ) := rfl

theorem inv_formula (v : E m) :
    ((wt m v : ℝ) : ℂ) = ∫ ξ, cexp (((2 * π * ⟪ξ, v⟫ : ℝ) : ℂ) * I) * Wh m ξ := by
  have h := (W m).continuous.fourierInv_fourier_eq (W m).integrable (Wh m).integrable
  have h2 := congrFun h v
  rw [Real.fourierInv_eq'] at h2
  rw [← W_apply, ← h2]
  rfl

/-! ## The Fourier transform of the paraboloid measure as an oscillatory integral -/

/-- The phase factor `e(-(⟪v, x̲⟫ + xₙ‖v‖²/2))`. -/
noncomputable def ph (x : E (m + 1)) (v : E m) : ℂ :=
  cexp (((2 * π * -(⟪v, horiz x⟫ + ‖v‖ ^ 2 / 2 * vert x) : ℝ) : ℂ) * I)

theorem norm_ph (x : E (m + 1)) (v : E m) : ‖ph x v‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem continuous_ph (x : E (m + 1)) : Continuous (ph x) := by
  unfold ph; fun_prop

theorem ft_eq (x : E (m + 1)) :
    ftMeasure (parabMeasure m) x = ∫ v, ((wt m v : ℝ) : ℂ) * ph x v := by
  unfold ftMeasure parabMeasure
  rw [integral_map continuous_graphPt.aemeasurable
    (by apply Continuous.aestronglyMeasurable; fun_prop)]
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable fun v : E m => ENNReal.ofReal (wt m v) from
      ENNReal.measurable_ofReal.comp (wBump m).continuous.measurable)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  have h1 : (ENNReal.ofReal (wt m v)).toReal = wt m v :=
    ENNReal.toReal_ofReal ((wBump m).nonneg' v)
  have h2 : ((𝐞 (-⟪graphPt v, x⟫) : ℂ)) = ph x v := by
    rw [inner_graphPt]; rfl
  change (ENNReal.ofReal (wt m v)).toReal • ((𝐞 (-⟪graphPt v, x⟫) : ℂ)) = ((wt m v : ℝ) : ℂ) * ph x v
  rw [h1, h2, Complex.real_smul]

/-- The damped integral `I_ε`. -/
noncomputable def Ieps (x : E (m + 1)) (ε : ℝ) : ℂ :=
  ∫ v, cexp (-(ε : ℂ) * ‖v‖ ^ 2) * (((wt m v : ℝ) : ℂ) * ph x v)

theorem tendsto_Ieps (x : E (m + 1)) :
    Tendsto (Ieps x) (𝓝[>] 0) (𝓝 (∫ v, ((wt m v : ℝ) : ℂ) * ph x v)) := by
  have hw : Continuous fun v : E m => ((wt m v : ℝ) : ℂ) := (W m).continuous
  have hph := continuous_ph x
  unfold Ieps
  apply tendsto_integral_filter_of_dominated_convergence (fun v => ‖W m v‖)
  · exact Eventually.of_forall fun ε => by
      apply Continuous.aestronglyMeasurable
      fun_prop
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine ae_of_all _ fun v => ?_
    have he : (-(ε : ℂ) * ‖v‖ ^ 2) = ((-ε * ‖v‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, norm_mul, norm_ph, mul_one, W_apply, he, Complex.norm_exp_ofReal]
    calc Real.exp (-ε * ‖v‖ ^ 2) * ‖((wt m v : ℝ) : ℂ)‖ ≤ 1 * ‖((wt m v : ℝ) : ℂ)‖ :=
          mul_le_mul_of_nonneg_right
            (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖v‖])) (norm_nonneg _)
      _ = _ := one_mul _
  · exact (W m).integrable.norm
  · refine ae_of_all _ fun v => ?_
    have hc : Continuous fun ε : ℝ =>
        cexp (-(ε : ℂ) * ‖v‖ ^ 2) * (((wt m v : ℝ) : ℂ) * ph x v) := by fun_prop
    have := hc.tendsto 0
    simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul] at this
    exact this.mono_left nhdsWithin_le_nhds

/-- `b = ε + π i xₙ`. -/
noncomputable def bb (x : E (m + 1)) (ε : ℝ) : ℂ := (ε : ℂ) + ((π * vert x : ℝ) : ℂ) * I

theorem Ieps_eq (x : E (m + 1)) {ε : ℝ} (hε : 0 < ε) :
    Ieps x ε = ∫ ξ, Wh m ξ * ((π / bb x ε) ^ (Module.finrank ℝ (E m) / 2 : ℂ) *
      cexp ((2 * π * I) ^ 2 * ‖ξ - horiz x‖ ^ 2 / (4 * bb x ε))) := by
  have hb : 0 < (bb x ε).re := by simp [bb, hε]
  have key : ∀ v ξ : E m, cexp (-(ε : ℂ) * ‖v‖ ^ 2) *
      (cexp (((2 * π * ⟪ξ, v⟫ : ℝ) : ℂ) * I) * Wh m ξ * ph x v) =
      Wh m ξ * cexp (-bb x ε * ‖v‖ ^ 2 + (2 * π * I) * ⟪ξ - horiz x, v⟫) := by
    intro v ξ
    unfold ph bb
    rw [inner_sub_left, real_inner_comm v (horiz x)]
    calc _ = Wh m ξ * (cexp (-(ε : ℂ) * ‖v‖ ^ 2) * cexp (((2 * π * ⟪ξ, v⟫ : ℝ) : ℂ) * I) *
          cexp (((2 * π * -(⟪v, horiz x⟫ + ‖v‖ ^ 2 / 2 * vert x) : ℝ) : ℂ) * I)) := by ring
      _ = _ := by
          rw [← Complex.exp_add, ← Complex.exp_add]
          congr 2
          push_cast
          ring
  have h1 : ∀ v : E m, cexp (-(ε : ℂ) * ‖v‖ ^ 2) * (((wt m v : ℝ) : ℂ) * ph x v) =
      ∫ ξ, Wh m ξ * cexp (-bb x ε * ‖v‖ ^ 2 + (2 * π * I) * ⟪ξ - horiz x, v⟫) := by
    intro v
    rw [inv_formula v, ← integral_mul_const, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun ξ => key v ξ)
  have hint : Integrable (Function.uncurry fun (v : E m) (ξ : E m) =>
      Wh m ξ * cexp (-bb x ε * ‖v‖ ^ 2 + (2 * π * I) * ⟪ξ - horiz x, v⟫))
      (volume.prod volume) := by
    have hg : Integrable (fun v : E m => cexp (-(ε : ℂ) * ‖v‖ ^ 2 + 0 * ⟪(0 : E m), v⟫)) :=
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa using hε) 0 0
    refine (hg.norm.mul_prod (Wh m).integrable.norm).mono' ?_ (ae_of_all _ fun z => ?_)
    · apply Continuous.aestronglyMeasurable
      have := (Wh m).continuous
      fun_prop
    · obtain ⟨v, ξ⟩ := z
      simp only [Function.uncurry_apply_pair, norm_mul]
      rw [mul_comm]
      apply le_of_eq
      congr 1
      rw [Complex.norm_exp, Complex.norm_exp, ← Complex.ofReal_pow]
      congr 1
      simp [bb, Complex.mul_re]
      right
      rw [← Complex.ofReal_pow, Complex.ofReal_im]
  unfold Ieps
  rw [integral_congr_ae (ae_of_all _ h1), integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb]

theorem gauss_bound (x : E (m + 1)) {ε : ℝ} (hε : 0 < ε) (ht : vert x ≠ 0) (w : E m) :
    ‖(π / bb x ε) ^ (Module.finrank ℝ (E m) / 2 : ℂ) *
      cexp ((2 * π * I) ^ 2 * ‖w‖ ^ 2 / (4 * bb x ε))‖ ≤ (|vert x|⁻¹) ^ ((m : ℝ) / 2) := by
  have hbre : (bb x ε).re = ε := by simp [bb]
  have hb0 : bb x ε ≠ 0 := fun h => by
    have := congrArg Complex.re h
    rw [hbre, Complex.zero_re] at this
    linarith
  have hfin : (Module.finrank ℝ (E m) / 2 : ℂ) = (((m : ℝ) / 2 : ℝ) : ℂ) := by
    rw [finrank_euclideanSpace_fin]; push_cast; ring
  rw [norm_mul, hfin, Complex.norm_cpow_real]
  have ht' : 0 < |vert x| := abs_pos.2 ht
  have hnb : π * |vert x| ≤ ‖bb x ε‖ := by
    have := Complex.abs_im_le_norm (bb x ε)
    have him : (bb x ε).im = π * vert x := by simp [bb]
    rw [him, abs_mul, abs_of_pos Real.pi_pos] at this
    exact this
  have hbpos : 0 < ‖bb x ε‖ := norm_pos_iff.2 hb0
  have h1 : ‖(π : ℂ) / bb x ε‖ ≤ |vert x|⁻¹ := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, div_le_iff₀ hbpos,
      inv_mul_eq_div, le_div_iff₀ ht']
    linarith
  have h2 : ‖cexp ((2 * π * I) ^ 2 * ‖w‖ ^ 2 / (4 * bb x ε))‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    have hI : (2 * (π : ℂ) * I) ^ 2 = -4 * π ^ 2 := by rw [mul_pow, I_sq]; ring
    have : (2 * π * I) ^ 2 * (‖w‖ : ℂ) ^ 2 / (4 * bb x ε) =
        ((-(π ^ 2 * ‖w‖ ^ 2) : ℝ) : ℂ) * (bb x ε)⁻¹ := by
      rw [hI]; push_cast; field_simp
    rw [this, Complex.re_ofReal_mul, Complex.inv_re, hbre]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity))
      (div_nonneg hε.le (Complex.normSq_nonneg _))
  calc ‖(π : ℂ) / bb x ε‖ ^ ((m : ℝ) / 2) * ‖cexp ((2 * π * I) ^ 2 * ‖w‖ ^ 2 / (4 * bb x ε))‖
      ≤ (|vert x|⁻¹) ^ ((m : ℝ) / 2) * 1 :=
        mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) h1 (by positivity)) h2 (norm_nonneg _)
          (by positivity)
    _ = _ := mul_one _

theorem parab_decay_vert (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, ∀ x : E (m + 1), ‖ftMeasure (parabMeasure m) x‖ * |vert x| ^ ((m : ℝ) / 2) ≤ C := by
  refine ⟨∫ ξ, ‖Wh m ξ‖, fun x => ?_⟩
  have hm2 : (0 : ℝ) < (m : ℝ) / 2 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  by_cases ht : vert x = 0
  · rw [ht, abs_zero, Real.zero_rpow hm2.ne', mul_zero]
    exact integral_nonneg fun _ => norm_nonneg _
  · have hbound : ‖ftMeasure (parabMeasure m) x‖ ≤
        (∫ ξ, ‖Wh m ξ‖) * (|vert x|⁻¹) ^ ((m : ℝ) / 2) := by
      rw [ft_eq]
      apply le_of_tendsto (tendsto_Ieps x).norm
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [Ieps_eq x hε, ← integral_mul_const]
      refine norm_integral_le_of_norm_le ((Wh m).integrable.norm.mul_const _)
        (ae_of_all _ fun ξ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (gauss_bound x hε ht _) (norm_nonneg _)
    calc ‖ftMeasure (parabMeasure m) x‖ * |vert x| ^ ((m : ℝ) / 2)
        ≤ (∫ ξ, ‖Wh m ξ‖) * (|vert x|⁻¹) ^ ((m : ℝ) / 2) * |vert x| ^ ((m : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = ∫ ξ, ‖Wh m ξ‖ := by
          rw [mul_assoc, ← Real.mul_rpow (by positivity) (by positivity),
            inv_mul_cancel₀ (abs_ne_zero.2 ht), Real.one_rpow, mul_one]

end TaoBR.Parab.PartG

end S_PartG

namespace TaoBR.Parab
alias parab_decay_vert := TaoBR.Parab.PartG.parab_decay_vert
end TaoBR.Parab

section S_PartH

/-! # Part H: `parab_decay_horiz` (horizontal Fourier decay of the paraboloid measure) -/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace


namespace TaoBR.Parab.PartH

open TaoBR.Parab Filter Complex
open scoped Topology Real

/-! ## Coordinates (copied from `PartG.lean`) -/

section Coords

variable {m : ℕ}

@[simp] theorem mkPoint_castSucc (u : E m) (t : ℝ) (i : Fin m) :
    mkPoint u t (Fin.castSucc i) = u i := by
  simp [mkPoint]

@[simp] theorem mkPoint_last (u : E m) (t : ℝ) : mkPoint u t (Fin.last m) = t := by
  simp [mkPoint]

@[simp] theorem horiz_apply (y : E (m + 1)) (i : Fin m) : horiz y i = y (Fin.castSucc i) := by
  simp [horiz]

theorem continuous_mkPoint : Continuous fun q : E m × ℝ => mkPoint q.1 q.2 := by
  unfold mkPoint
  apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp
  apply continuous_pi; intro i
  induction i using Fin.lastCases with
  | last => simp; fun_prop
  | cast j => simp; fun_prop

theorem continuous_graphPt : Continuous (graphPt : E m → E (m + 1)) :=
  continuous_mkPoint.comp (continuous_id.prodMk (by fun_prop))

theorem inner_graphPt (v : E m) (x : E (m + 1)) :
    ⟪graphPt v, x⟫ = ⟪v, horiz x⟫ + ‖v‖ ^ 2 / 2 * vert x := by
  simp only [graphPt, PiLp.inner_apply, Fin.sum_univ_castSucc, mkPoint_castSucc, mkPoint_last,
    horiz_apply, vert]
  simp [mul_comm]

end Coords

variable {m : ℕ}

theorem hasCompactSupport_wC (m : ℕ) : HasCompactSupport fun v : E m => ((wt m v : ℝ) : ℂ) :=
  (wBump m).hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero

theorem continuous_wC (m : ℕ) : Continuous fun v : E m => ((wt m v : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (wBump m).continuous

/-! ## The Fourier transform of the paraboloid measure as an oscillatory integral (from `PartG`) -/

/-- The phase factor `e(-(⟪v, x̲⟫ + xₙ‖v‖²/2))`. -/
noncomputable def ph (x : E (m + 1)) (v : E m) : ℂ :=
  cexp (((2 * π * -(⟪v, horiz x⟫ + ‖v‖ ^ 2 / 2 * vert x) : ℝ) : ℂ) * I)

theorem norm_ph (x : E (m + 1)) (v : E m) : ‖ph x v‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem continuous_ph (x : E (m + 1)) : Continuous (ph x) := by
  unfold ph; fun_prop

theorem ft_eq (x : E (m + 1)) :
    ftMeasure (parabMeasure m) x = ∫ v, ((wt m v : ℝ) : ℂ) * ph x v := by
  unfold ftMeasure parabMeasure
  rw [integral_map continuous_graphPt.aemeasurable
    (by apply Continuous.aestronglyMeasurable; fun_prop)]
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable fun v : E m => ENNReal.ofReal (wt m v) from
      ENNReal.measurable_ofReal.comp (wBump m).continuous.measurable)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  have h1 : (ENNReal.ofReal (wt m v)).toReal = wt m v :=
    ENNReal.toReal_ofReal ((wBump m).nonneg' v)
  have h2 : ((𝐞 (-⟪graphPt v, x⟫) : ℂ)) = ph x v := by
    rw [inner_graphPt]; rfl
  change (ENNReal.ofReal (wt m v)).toReal • ((𝐞 (-⟪graphPt v, x⟫) : ℂ)) = ((wt m v : ℝ) : ℂ) * ph x v
  rw [h1, h2, Complex.real_smul]

/-! ## Directional derivatives along a line -/

theorem fderiv_apply_of_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E m → F} {v a : E m} {d : F} (hf : DifferentiableAt ℝ f v)
    (h : HasDerivAt (fun s : ℝ => f (v + s • a)) d 0) : fderiv ℝ f v a = d := by
  have h1 : HasDerivAt (fun s : ℝ => v + s • a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add v
  have := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
  exact this.unique h

theorem hasDerivAt_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E m → F} {v a : E m} (hf : DifferentiableAt ℝ f v) :
    HasDerivAt (fun s : ℝ => f (v + s • a)) (fderiv ℝ f v a) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => v + s • a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add v
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)

/-! ## The phase and its derivative in direction `x̲` -/

/-- `q(v) = ‖x̲‖² + xₙ ⟪v, x̲⟫`, the derivative of the phase in direction `x̲`. -/
noncomputable def qf (x : E (m + 1)) (v : E m) : ℝ := ‖horiz x‖ ^ 2 + vert x * ⟪v, horiz x⟫

theorem differentiable_ph (x : E (m + 1)) : Differentiable ℝ (ph x) := by
  have h1 : Differentiable ℝ fun v : E m => ⟪v, horiz x⟫ :=
    differentiable_id.inner ℝ (differentiable_const _)
  have h2 : Differentiable ℝ fun v : E m => ‖v‖ ^ 2 := differentiable_id.norm_sq ℝ
  unfold ph; fun_prop

theorem fderiv_ph (x : E (m + 1)) (v : E m) :
    fderiv ℝ (ph x) v (horiz x) = ph x v * (((-(2 * π * qf x v)) : ℝ) * I) := by
  apply fderiv_apply_of_line (differentiable_ph x v)
  have hfun : (fun s : ℝ => ph x (v + s • horiz x)) =
      fun s : ℝ => cexp (((2 * π * -(⟪v, horiz x⟫ + ‖v‖ ^ 2 / 2 * vert x) +
        (-(2 * π * qf x v)) * s + (-(π * vert x * ‖horiz x‖ ^ 2)) * s ^ 2 : ℝ) : ℂ) * I) := by
    funext s
    unfold ph
    congr 3
    simp only [qf, inner_add_left, inner_smul_left, inner_smul_right, norm_add_sq_real, norm_smul,
      real_inner_self_eq_norm_sq, RCLike.conj_to_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hpoly : HasDerivAt (fun s : ℝ => 2 * π * -(⟪v, horiz x⟫ + ‖v‖ ^ 2 / 2 * vert x) +
        (-(2 * π * qf x v)) * s + (-(π * vert x * ‖horiz x‖ ^ 2)) * s ^ 2)
      (-(2 * π * qf x v)) 0 := by
    refine HasDerivAt.congr_deriv (((hasDerivAt_const (0 : ℝ)
      (2 * π * -(⟪v, horiz x⟫ + ‖v‖ ^ 2 / 2 * vert x))).add
      ((hasDerivAt_id' (0 : ℝ)).const_mul (-(2 * π * qf x v)))).add
      ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (-(π * vert x * ‖horiz x‖ ^ 2)))) ?_
    norm_num
  have := ((hpoly.ofReal_comp).mul_const I).cexp
  rw [hfun]
  refine this.congr_deriv ?_
  unfold ph
  congr 4
  ring

/-! ## The amplitude `h = w / (-2πi q)` -/

theorem wt_eq_zero {v : E m} (hv : 5 / 4 ≤ ‖v‖) : wt m v = 0 := by
  have : v ∉ Function.support (wBump m) := by
    rw [(wBump m).support_eq]
    simp only [Metric.mem_ball, dist_zero_right, not_lt]
    exact hv
  exact Function.notMem_support.1 this

theorem wt_le_one (v : E m) : wt m v ≤ 1 := (wBump m).le_one

theorem wt_nonneg (v : E m) : 0 ≤ wt m v := (wBump m).nonneg' v

theorem differentiable_wt : Differentiable ℝ (wt m) :=
  ((wBump m).contDiff (n := 1)).differentiable (by norm_num)

theorem qf_ge {x : E (m + 1)} (hx : 4 * |vert x| ≤ ‖horiz x‖) {v : E m} (hv : ‖v‖ ≤ 3 / 2) :
    5 / 8 * ‖horiz x‖ ^ 2 ≤ qf x v := by
  unfold qf
  have h1 : |vert x * ⟪v, horiz x⟫| ≤ |vert x| * (‖v‖ * ‖horiz x‖) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
  have h2 : |vert x| * (‖v‖ * ‖horiz x‖) ≤ (‖horiz x‖ / 4) * (3 / 2 * ‖horiz x‖) :=
    mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right hv (norm_nonneg _)) (by positivity)
      (by positivity)
  have h3 := neg_abs_le (vert x * ⟪v, horiz x⟫)
  nlinarith

theorem qf_pos {x : E (m + 1)} (hx : 4 * |vert x| ≤ ‖horiz x‖) (ha : horiz x ≠ 0) {v : E m}
    (hv : ‖v‖ ≤ 3 / 2) : 0 < qf x v := by
  have := qf_ge hx hv
  have : 0 < ‖horiz x‖ := norm_pos_iff.2 ha
  have : 0 < 5 / 8 * ‖horiz x‖ ^ 2 := by positivity
  linarith

/-- `h_ℝ(v) = w(v) / q(v)`. -/
noncomputable def hR (x : E (m + 1)) (v : E m) : ℝ := wt m v * (qf x v)⁻¹

/-- The constant `(-2πi)⁻¹`. -/
noncomputable def cc : ℂ := (-(2 * (π : ℂ) * I))⁻¹

/-- `h(v) = w(v) / (-2πi q(v))`. -/
noncomputable def hC (x : E (m + 1)) (v : E m) : ℂ := ((hR x v : ℝ) : ℂ) * cc

theorem hC_eventually_zero (x : E (m + 1)) {v : E m} (hv : 5 / 4 < ‖v‖) :
    hC x =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
  have : {u : E m | 5 / 4 < ‖u‖} ∈ 𝓝 v :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hv
  filter_upwards [this] with u hu
  simp [hC, hR, wt_eq_zero (le_of_lt hu)]

theorem differentiableAt_hC {x : E (m + 1)} (hx : 4 * |vert x| ≤ ‖horiz x‖)
    (ha : horiz x ≠ 0) (v : E m) : DifferentiableAt ℝ (hC x) v := by
  by_cases hv : ‖v‖ < 3 / 2
  · have hq : qf x v ≠ 0 := by
      exact (qf_pos hx ha hv.le).ne'
    have hqd : Differentiable ℝ (qf x) := by
      have h1 : Differentiable ℝ fun v : E m => ⟪v, horiz x⟫ :=
        differentiable_id.inner ℝ (differentiable_const _)
      unfold qf; fun_prop
    have : DifferentiableAt ℝ (hR x) v :=
      (differentiable_wt v).mul ((hqd v).inv hq)
    unfold hC
    exact (Complex.ofRealCLM.differentiableAt.comp v this).mul_const _
  · exact ((hC_eventually_zero x (by linarith : (5 : ℝ) / 4 < ‖v‖)).differentiableAt_iff).2
      (differentiableAt_const _)

theorem fderiv_hC_far (x : E (m + 1)) {v : E m} (hv : 5 / 4 < ‖v‖) (a : E m) :
    fderiv ℝ (hC x) v a = 0 := by
  rw [(hC_eventually_zero x hv).fderiv_eq]
  simp

theorem fderiv_hC_near {x : E (m + 1)} (hx : 4 * |vert x| ≤ ‖horiz x‖)
    (ha : horiz x ≠ 0) {v : E m} (hv : ‖v‖ < 3 / 2) :
    fderiv ℝ (hC x) v (horiz x) =
      (((fderiv ℝ (wt m) v (horiz x) * (qf x v)⁻¹ +
        wt m v * (-(vert x * ‖horiz x‖ ^ 2) / (qf x v) ^ 2) : ℝ) : ℂ)) * cc := by
  have hq : qf x v ≠ 0 := by
    exact (qf_pos hx ha hv.le).ne'
  apply fderiv_apply_of_line (differentiableAt_hC hx ha v)
  have hw := hasDerivAt_line (a := horiz x) (differentiable_wt (m := m) v)
  have hfun : (fun s : ℝ => qf x (v + s • horiz x)) =
      fun s : ℝ => qf x v + (vert x * ‖horiz x‖ ^ 2) * s := by
    funext s
    simp only [qf, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq,
      RCLike.conj_to_real]
    ring
  have hqd : HasDerivAt (fun s : ℝ => qf x (v + s • horiz x)) (vert x * ‖horiz x‖ ^ 2) 0 := by
    rw [hfun]
    refine HasDerivAt.congr_deriv ((hasDerivAt_const (0 : ℝ) (qf x v)).add
      ((hasDerivAt_id' (0 : ℝ)).const_mul (vert x * ‖horiz x‖ ^ 2))) ?_
    ring
  have hqi := hqd.inv (by simpa using hq)
  have := ((hw.mul hqi).ofReal_comp).mul_const cc
  unfold hC hR
  refine this.congr_deriv ?_
  simp

theorem hC_mul_fderiv_ph {x : E (m + 1)} (hx : 4 * |vert x| ≤ ‖horiz x‖)
    (ha : horiz x ≠ 0) (v : E m) :
    hC x v * fderiv ℝ (ph x) v (horiz x) = ((wt m v : ℝ) : ℂ) * ph x v := by
  rw [fderiv_ph]
  by_cases hw : wt m v = 0
  · simp [hC, hR, hw]
  · have hv : ‖v‖ < 3 / 2 := by
      by_contra h
      exact hw (wt_eq_zero (by linarith))
    have hq : qf x v ≠ 0 := by
      exact (qf_pos hx ha hv.le).ne'
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hq' : (qf x v : ℂ) ≠ 0 := by exact_mod_cast hq
    unfold hC hR cc
    push_cast
    field_simp

theorem norm_cc : ‖cc‖ = (2 * π)⁻¹ := by
  unfold cc
  rw [norm_inv, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]

/-! ## The pointwise bound on the derivative of the amplitude -/

theorem deriv_bound {A M D w t q : ℝ} (hA : 0 < A) (hM : 0 ≤ M) (hD : |D| ≤ M * A)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (ht : 4 * |t| ≤ A) (hq : 5 / 8 * A ^ 2 ≤ q) :
    |D * q⁻¹ + w * (-(t * A ^ 2) / q ^ 2)| ≤ (2 * M + 1) / A := by
  have hqpos : 0 < q := lt_of_lt_of_le (by positivity) hq
  have h1 : |D * q⁻¹| ≤ 2 * M / A := by
    rw [abs_mul, abs_inv, abs_of_pos hqpos, ← div_eq_mul_inv, div_le_div_iff₀ hqpos hA]
    have := mul_le_mul_of_nonneg_right hD hA.le
    have := mul_le_mul_of_nonneg_left hq hM
    nlinarith [sq_nonneg A]
  have h2 : |w * (-(t * A ^ 2) / q ^ 2)| ≤ 1 / A := by
    rw [abs_mul, abs_div, abs_neg, abs_mul, abs_of_nonneg hw0, abs_of_nonneg (sq_nonneg A),
      abs_of_pos (pow_pos hqpos 2)]
    have hq2 : (5 / 8 * A ^ 2) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by positivity) hq 2
    have h3 : |t| * A ^ 2 / q ^ 2 ≤ 1 / A := by
      rw [div_le_div_iff₀ (pow_pos hqpos 2) hA]
      have : |t| * A ^ 2 * A ≤ A / 4 * A ^ 2 * A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg A)) hA.le
      nlinarith [pow_pos hA 4]
    calc w * (|t| * A ^ 2 / q ^ 2) ≤ 1 * (|t| * A ^ 2 / q ^ 2) :=
          mul_le_mul_of_nonneg_right hw1 (by positivity)
      _ ≤ 1 / A := by rw [one_mul]; exact h3
  calc _ ≤ |D * q⁻¹| + |w * (-(t * A ^ 2) / q ^ 2)| := abs_add_le _ _
    _ ≤ 2 * M / A + 1 / A := add_le_add h1 h2
    _ = (2 * M + 1) / A := by ring

theorem hasCompactSupport_hC (x : E (m + 1)) : HasCompactSupport (hC x) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E m) (5 / 4)) fun v hv => ?_
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hv
  simp [hC, hR, wt_eq_zero hv.le]

theorem parab_decay_horiz (m : ℕ) :
    ∃ C : ℝ, ∀ x : E (m + 1), 4 * |vert x| ≤ ‖horiz x‖ →
      ‖ftMeasure (parabMeasure m) x‖ * ‖horiz x‖ ≤ C := by
  obtain ⟨M0, hM0⟩ := (((wBump m).contDiff (n := 1)).continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    ((wBump m).hasCompactSupport.fderiv (𝕜 := ℝ))
  have hwt : wt m = ⇑(wBump m) := rfl
  set M := max M0 0 with hMdef
  set V := (volume : Measure (E m)).real (ball (0 : E m) (3 / 2)) with hVdef
  have hV : 0 ≤ V := measureReal_nonneg
  refine ⟨(2 * M + 1) / (2 * Real.pi) * V, fun x hx => ?_⟩
  have hM : 0 ≤ M := le_max_right _ _
  by_cases ha : horiz x = 0
  · rw [ha, norm_zero, mul_zero]; positivity
  have hA : 0 < ‖horiz x‖ := norm_pos_iff.2 ha
  set K := (2 * M + 1) / (2 * Real.pi) / ‖horiz x‖ with hKdef
  have hbound : ∀ v, ‖fderiv ℝ (hC x) v (horiz x) * ph x v‖ ≤
      (ball (0 : E m) (3 / 2)).indicator (fun _ => K) v := by
    intro v
    rw [norm_mul, norm_ph, mul_one]
    by_cases hv : ‖v‖ < 3 / 2
    · rw [indicator_of_mem (by simpa using hv), fderiv_hC_near hx ha hv, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, norm_cc, hKdef]
      have hD : |fderiv ℝ (wt m) v (horiz x)| ≤ M * ‖horiz x‖ := by
        rw [← Real.norm_eq_abs]
        refine (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        rw [hwt]
        exact (hM0 v).trans (le_max_left _ _)
      have := deriv_bound hA hM hD (wt_nonneg v) (wt_le_one v) hx (qf_ge hx hv.le)
      rw [div_div, mul_comm (2 * Real.pi), ← div_div, div_eq_mul_inv _ (2 * Real.pi)]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    · rw [fderiv_hC_far x (by linarith), norm_zero]
      exact Set.indicator_nonneg (fun _ _ => by positivity) _
  have hint_bound : Integrable ((ball (0 : E m) (3 / 2)).indicator (fun _ => K)) :=
    (integrableOn_const measure_ball_lt_top.ne).integrable_indicator measurableSet_ball
  have hf'g : Integrable fun v => fderiv ℝ (hC x) v (horiz x) * ph x v :=
    hint_bound.mono' (((measurable_fderiv_apply_const ℝ (hC x) (horiz x)).mul
      (continuous_ph x).measurable).aestronglyMeasurable) (ae_of_all _ hbound)
  have hfg' : Integrable fun v => hC x v * fderiv ℝ (ph x) v (horiz x) := by
    have : (fun v => hC x v * fderiv ℝ (ph x) v (horiz x)) =
        fun v => ((wt m v : ℝ) : ℂ) * ph x v := funext (hC_mul_fderiv_ph hx ha)
    rw [this]
    exact ((continuous_wC m).mul (continuous_ph x)).integrable_of_hasCompactSupport
      (hasCompactSupport_wC m).mul_right
  have hcont : Continuous (hC x) :=
    continuous_iff_continuousAt.2 fun v => (differentiableAt_hC hx ha v).continuousAt
  have hfg : Integrable fun v => hC x v * ph x v :=
    (hcont.mul (continuous_ph x)).integrable_of_hasCompactSupport
      (hasCompactSupport_hC x).mul_right
  have e1 : ∫ v, ((wt m v : ℝ) : ℂ) * ph x v = ∫ v, hC x v * fderiv ℝ (ph x) v (horiz x) :=
    integral_congr_ae (ae_of_all _ fun v => (hC_mul_fderiv_ph hx ha v).symm)
  rw [ft_eq, e1, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg
    (fun v _ => differentiableAt_hC hx ha v) (fun v _ => differentiable_ph x v), norm_neg]
  have := norm_integral_le_of_norm_le hint_bound (ae_of_all _ hbound)
  rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul] at this
  calc _ ≤ V * K * ‖horiz x‖ := mul_le_mul_of_nonneg_right this hA.le
    _ = (2 * M + 1) / (2 * Real.pi) * V := by rw [hKdef]; field_simp

end TaoBR.Parab.PartH

end S_PartH

namespace TaoBR.Parab
alias parab_decay_horiz := TaoBR.Parab.PartH.parab_decay_horiz
end TaoBR.Parab

section S_PartI

/-! # Part I: `goodMeasure_parab`, `exists_good_exponent`, `parabolic_of_restrMu` -/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace


namespace TaoBR.Parab.PartI

open TaoBR.Parab Filter
open scoped Topology Real

/-! ## Coordinates (copied from `PartF.lean`, `PartH.lean`) -/

section Coords

variable {m : ℕ}

@[simp] theorem mkPoint_castSucc (u : E m) (t : ℝ) (i : Fin m) :
    mkPoint u t (Fin.castSucc i) = u i := by
  simp [mkPoint]

@[simp] theorem mkPoint_last (u : E m) (t : ℝ) : mkPoint u t (Fin.last m) = t := by
  simp [mkPoint]

@[simp] theorem horiz_apply (y : E (m + 1)) (i : Fin m) : horiz y i = y (Fin.castSucc i) := by
  simp [horiz]

@[simp] theorem horiz_mkPoint (u : E m) (t : ℝ) : horiz (mkPoint u t) = u := by
  ext i; simp

@[simp] theorem vert_mkPoint (u : E m) (t : ℝ) : vert (mkPoint u t) = t := by
  simp [vert]

theorem mkPoint_horiz_vert (ξ : E (m + 1)) : mkPoint (horiz ξ) (vert ξ) = ξ := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [vert]
  | cast j => simp

theorem mkPoint_sub (u u' : E m) (t t' : ℝ) :
    mkPoint u t - mkPoint u' t' = mkPoint (u - u') (t - t') := by
  ext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

theorem norm_mkPoint_sq (u : E m) (t : ℝ) : ‖mkPoint u t‖ ^ 2 = ‖u‖ ^ 2 + t ^ 2 := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), Fin.sum_univ_castSucc]
  simp

theorem continuous_mkPoint : Continuous fun q : E m × ℝ => mkPoint q.1 q.2 := by
  unfold mkPoint
  apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp
  apply continuous_pi; intro i
  induction i using Fin.lastCases with
  | last => simp; fun_prop
  | cast j => simp; fun_prop

theorem continuous_graphPt : Continuous (graphPt : E m → E (m + 1)) :=
  continuous_mkPoint.comp (continuous_id.prodMk (by fun_prop))

theorem norm_sq_split (x : E (m + 1)) : ‖x‖ ^ 2 = ‖horiz x‖ ^ 2 + vert x ^ 2 := by
  conv_lhs => rw [← mkPoint_horiz_vert x]
  exact norm_mkPoint_sq _ _

theorem norm_le_horiz_add_vert (x : E (m + 1)) : ‖x‖ ≤ ‖horiz x‖ + |vert x| := by
  have h := norm_sq_split x
  have h1 : vert x ^ 2 = |vert x| ^ 2 := (sq_abs _).symm
  nlinarith [norm_nonneg x, norm_nonneg (horiz x), abs_nonneg (vert x)]

end Coords

variable {m : ℕ}

theorem wt_eq_zero {v : E m} (hv : 5 / 4 ≤ ‖v‖) : wt m v = 0 := by
  have : v ∉ Function.support (wBump m) := by
    rw [(wBump m).support_eq]
    simp only [Metric.mem_ball, dist_zero_right, not_lt]
    exact hv
  exact Function.notMem_support.1 this

theorem wt_le_one (v : E m) : wt m v ≤ 1 := (wBump m).le_one

theorem continuous_wt : Continuous (wt m) := (wBump m).continuous

/-! ## `exists_good_exponent` -/

/-- **N1 (choice of the exponent).** For `1 ≤ q < p_c` there is `p ∈ (1, p_c)` with
`0 < α(p) < α₀` and `1/p + κ / log(1/α(p)) < 1/q`.

Proof: `α(p) → 0⁺` as `p ↑ p_c` (continuous, `α(p_c) = 0`, strictly decreasing in `p`), so
`κ / log(1/α(p)) → 0`, while `1/p → 1/p_c < 1/q`; `p_c > 1` as `m ≥ 1`, `p_c < 2`. -/
theorem exists_good_exponent (m : ℕ) (hm : 1 ≤ m) (κ α₀ : ℝ) (hα₀ : 0 < α₀) {q : ℝ}
    (hq : 1 ≤ q) (hqc : q < 2 * ((m : ℝ) + 1) / ((m : ℝ) + 2)) :
    ∃ p : ℝ, 1 < p ∧ p < 2 ∧ p < 2 * ((m : ℝ) + 1) / ((m : ℝ) + 2) ∧
      0 < alphaPar m p ∧ alphaPar m p < α₀ ∧
      1 / p + κ / Real.log (1 / alphaPar m p) < 1 / q := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq0 : 0 < q := by linarith
  set a : ℝ := (m : ℝ) + 1 with ha
  set b : ℝ := (m : ℝ) + 2 with hb
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  -- the gap `δ = 1/q - 1/p_c`
  set δ : ℝ := 1 / q - b / (2 * a) with hδ
  have hδ0 : 0 < δ := by
    have : 2 * a / b = 2 * ((m : ℝ) + 1) / ((m : ℝ) + 2) := rfl
    rw [← this, lt_div_iff₀ hb0] at hqc
    rw [hδ, sub_pos, div_lt_div_iff₀ (by positivity) hq0]
    linarith
  set K : ℝ := 2 * |κ| / δ + 1 with hK
  have hK0 : 0 < K := by positivity
  set ε : ℝ := min (min α₀ (1 / 2)) (min δ (Real.exp (-K))) / 2 with hε
  have hε0 : 0 < ε := by
    rw [hε]; apply half_pos
    exact lt_min (lt_min hα₀ (by norm_num)) (lt_min hδ0 (Real.exp_pos _))
  have hεα : ε < α₀ := by
    have : min (min α₀ (1 / 2)) (min δ (Real.exp (-K))) ≤ α₀ :=
      (min_le_left _ _).trans (min_le_left _ _)
    rw [hε]; linarith
  have hεh : ε ≤ 1 / 4 := by
    have : min (min α₀ (1 / 2)) (min δ (Real.exp (-K))) ≤ 1 / 2 :=
      (min_le_left _ _).trans (min_le_right _ _)
    rw [hε]; linarith
  have hεδ : ε ≤ δ / 2 := by
    have : min (min α₀ (1 / 2)) (min δ (Real.exp (-K))) ≤ δ :=
      (min_le_right _ _).trans (min_le_left _ _)
    rw [hε]; linarith
  have hεK : ε < Real.exp (-K) := by
    have : min (min α₀ (1 / 2)) (min δ (Real.exp (-K))) ≤ Real.exp (-K) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have := Real.exp_pos (-K)
    rw [hε]; linarith
  set p : ℝ := 2 * a / (b + 2 * ε) with hp
  have hden : 0 < b + 2 * ε := by linarith
  have halpha : alphaPar m p = ε := by
    simp only [alphaPar, hp]
    rw [← ha, ← hb]
    field_simp
    ring
  have hinvp : 1 / p = b / (2 * a) + ε / a := by
    rw [hp]; field_simp
  have hpc : p < 2 * a / b := by
    rw [hp]; apply div_lt_div_of_pos_left (by positivity) hb0; linarith
  have hpc2 : 2 * a / b < 2 := by
    rw [div_lt_iff₀ hb0]; linarith
  refine ⟨p, ?_, hpc.trans hpc2, hpc, by rw [halpha]; exact hε0, by rw [halpha]; exact hεα, ?_⟩
  · rw [hp, lt_div_iff₀ hden]; linarith
  · rw [halpha, hinvp]
    have hlog : K < Real.log (1 / ε) := by
      rw [one_div, Real.log_inv, lt_neg]
      rw [← Real.exp_lt_exp, Real.exp_log hε0]
      exact hεK
    have hlogpos : 0 < Real.log (1 / ε) := hK0.trans hlog
    have h1 : κ / Real.log (1 / ε) < δ / 2 := by
      rw [div_lt_iff₀ hlogpos]
      have : |κ| < δ / 2 * K := by
        rw [hK]; field_simp; nlinarith [abs_nonneg κ]
      have h2 : δ / 2 * K ≤ δ / 2 * Real.log (1 / ε) :=
        mul_le_mul_of_nonneg_left hlog.le (by positivity)
      linarith [le_abs_self κ]
    have h3 : ε / a ≤ ε := div_le_self hε0.le (by linarith)
    have : b / (2 * a) + δ = 1 / q := by rw [hδ]; ring
    linarith

/-! ## `goodMeasure_parab` -/

theorem integrable_wt : Integrable (wt m) :=
  continuous_wt.integrable_of_hasCompactSupport (wBump m).hasCompactSupport

theorem measurable_graphPt : Measurable (graphPt : E m → E (m + 1)) :=
  continuous_graphPt.measurable

instance isFinite_dens : IsFiniteMeasure
    ((volume : Measure (E m)).withDensity fun v => ENNReal.ofReal (wt m v)) :=
  isFiniteMeasure_withDensity_ofReal integrable_wt.hasFiniteIntegral

theorem isFinite_parab : IsFiniteMeasure (parabMeasure m) := by
  unfold parabMeasure; infer_instance

theorem norm_graphPt_sq (v : E m) : ‖graphPt v‖ ^ 2 = ‖v‖ ^ 2 + (‖v‖ ^ 2 / 2) ^ 2 :=
  norm_mkPoint_sq _ _

theorem parabSet_subset : parabSet m ⊆ closedBall 0 (3 / 2) := by
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_closedBall, dist_zero_right] at hv ⊢
  have h := norm_graphPt_sq v
  have h0 := norm_nonneg v
  have h1 : ‖v‖ ^ 2 ≤ 25 / 16 := by nlinarith
  have h2 : ‖graphPt v‖ ^ 2 ≤ (3 / 2) ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 h2

theorem isCompact_parabSet : IsCompact (parabSet m) :=
  (isCompact_closedBall _ _).image continuous_graphPt

theorem parab_null_compl : parabMeasure m (parabSet m)ᶜ = 0 := by
  have hS : MeasurableSet (parabSet m)ᶜ := isCompact_parabSet.isClosed.measurableSet.compl
  unfold parabMeasure
  rw [Measure.map_apply measurable_graphPt hS, withDensity_apply _ (measurable_graphPt hS)]
  have : ∀ v ∈ graphPt ⁻¹' (parabSet m)ᶜ, ENNReal.ofReal (wt m v) = 0 := by
    intro v hv
    have hv' : v ∉ closedBall (0 : E m) (5 / 4) := fun h => hv ⟨v, h, rfl⟩
    rw [mem_closedBall, dist_zero_right, not_le] at hv'
    rw [wt_eq_zero hv'.le, ENNReal.ofReal_zero]
  rw [setLIntegral_congr_fun (measurable_graphPt hS) this, lintegral_zero]

theorem graphPt_mem_ball {η : E (m + 1)} {r : ℝ} {v : E m} (hv : graphPt v ∈ ball η r) :
    v ∈ ball (horiz η) r := by
  rw [mem_ball, dist_eq_norm] at hv ⊢
  have h : graphPt v - η = mkPoint (v - horiz η) (‖v‖ ^ 2 / 2 - vert η) := by
    conv_lhs => rw [← mkPoint_horiz_vert η]
    exact mkPoint_sub _ _ _ _
  have h2 := norm_mkPoint_sq (v - horiz η) (‖v‖ ^ 2 / 2 - vert η)
  rw [← h] at h2
  have : ‖v - horiz η‖ ≤ ‖graphPt v - η‖ := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    nlinarith [sq_nonneg (‖v‖ ^ 2 / 2 - vert η)]
  linarith

theorem parab_frostman (hm : 1 ≤ m) : ∃ C : ℝ, ∀ η : E (m + 1), ∀ r : ℝ, 0 < r →
    parabMeasure m (ball η r) ≤ ENNReal.ofReal (C * r ^ (m + 1 - 1)) := by
  have : Nontrivial (E m) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  refine ⟨(volume (ball (0 : E m) 1)).toReal, fun η r hr => ?_⟩
  unfold parabMeasure
  rw [Measure.map_apply measurable_graphPt measurableSet_ball,
    withDensity_apply _ (measurable_graphPt measurableSet_ball)]
  calc ∫⁻ v in graphPt ⁻¹' ball η r, ENNReal.ofReal (wt m v)
      ≤ ∫⁻ v in graphPt ⁻¹' ball η r, 1 := by
        gcongr with v
        exact ENNReal.ofReal_le_one.2 (wt_le_one v)
    _ = volume (graphPt ⁻¹' ball η r) := by rw [setLIntegral_one]
    _ ≤ volume (ball (horiz η) r) := measure_mono fun v hv => graphPt_mem_ball hv
    _ = ENNReal.ofReal ((volume (ball (0 : E m) 1)).toReal * r ^ (m + 1 - 1)) := by
        rw [Measure.addHaar_ball _ _ hr.le, finrank_euclideanSpace_fin, Nat.add_sub_cancel,
          ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal measure_ball_lt_top.ne,
          mul_comm]

theorem norm_ftMeasure_le (x : E (m + 1)) :
    ‖ftMeasure (parabMeasure m) x‖ ≤ (parabMeasure m).real univ := by
  have := isFinite_parab (m := m)
  unfold ftMeasure
  refine (norm_integral_le_of_norm_le_const (C := 1) (ae_of_all _ fun ξ => ?_)).trans
    (by rw [one_mul])
  exact (Circle.norm_coe _).le

theorem parab_decay (hm : 1 ≤ m) : ∃ C c : ℝ, 0 < c ∧
    ∀ x : E (m + 1), ‖ftMeasure (parabMeasure m) x‖ ≤ C * (1 + ‖x‖) ^ (-c) := by
  obtain ⟨C1, hC1⟩ := parab_decay_vert m hm
  obtain ⟨C2, hC2⟩ := parab_decay_horiz m
  set M := (parabMeasure m).real univ
  have hM : 0 ≤ M := measureReal_nonneg
  refine ⟨3 * (max C1 0 + max C2 0 + M), 1 / 2, by norm_num, fun x => ?_⟩
  set F := ‖ftMeasure (parabMeasure m) x‖
  have hF0 : 0 ≤ F := norm_nonneg _
  have hFM : F ≤ M := norm_ftMeasure_le x
  have hpos : 0 < 1 + ‖x‖ := by positivity
  set s := Real.sqrt (1 + ‖x‖) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hpos
  have hrw : (1 + ‖x‖) ^ (-(1 / 2 : ℝ)) = s⁻¹ := by
    rw [Real.rpow_neg hpos.le, hs, Real.sqrt_eq_rpow]
  rw [hrw, ← div_eq_mul_inv, le_div_iff₀ hs0]
  have hnx := norm_le_horiz_add_vert x
  have hA := norm_nonneg (horiz x)
  have hB := abs_nonneg (vert x)
  have hmax1 := le_max_left C1 0
  have hmax2 := le_max_left C2 0
  have hmax1' := le_max_right C1 0
  have hmax2' := le_max_right C2 0
  -- the main bound `F * s ≤ 3 * (C1⁺ + C2⁺ + M)`
  have key : F * s ≤ 3 * max C1 0 ∨ F * s ≤ 3 * max C2 0 ∨ F * s ≤ 3 * M := by
    by_cases hcase : 4 * |vert x| ≤ ‖horiz x‖
    · by_cases hA1 : 1 ≤ ‖horiz x‖
      · right; left
        have hsle : s ≤ 3 * ‖horiz x‖ := by
          rw [hs, Real.sqrt_le_iff]; constructor
          · positivity
          · nlinarith
        have := hC2 x hcase
        calc F * s ≤ F * (3 * ‖horiz x‖) := mul_le_mul_of_nonneg_left hsle hF0
          _ = 3 * (F * ‖horiz x‖) := by ring
          _ ≤ 3 * max C2 0 := by linarith
      · right; right
        have hsle : s ≤ 3 := by
          rw [hs, Real.sqrt_le_iff]; constructor
          · norm_num
          · push Not at hA1; nlinarith
        calc F * s ≤ M * 3 := mul_le_mul hFM hsle hs0.le hM
          _ = 3 * M := by ring
    · push Not at hcase
      by_cases hB1 : 1 ≤ |vert x|
      · left
        set t := Real.sqrt |vert x| with ht
        have hsle : s ≤ 3 * t := by
          rw [hs, Real.sqrt_le_iff]; constructor
          · positivity
          · rw [mul_pow, ht, Real.sq_sqrt hB]; nlinarith
        have htle : t ≤ |vert x| ^ ((m : ℝ) / 2) := by
          rw [ht, Real.sqrt_eq_rpow]
          apply Real.rpow_le_rpow_of_exponent_le hB1
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm
          linarith
        have := hC1 x
        calc F * s ≤ F * (3 * t) := mul_le_mul_of_nonneg_left hsle hF0
          _ ≤ F * (3 * |vert x| ^ ((m : ℝ) / 2)) := by gcongr
          _ = 3 * (F * |vert x| ^ ((m : ℝ) / 2)) := by ring
          _ ≤ 3 * max C1 0 := by linarith
      · right; right
        have hsle : s ≤ 3 := by
          rw [hs, Real.sqrt_le_iff]; constructor
          · norm_num
          · push Not at hB1; nlinarith
        calc F * s ≤ M * 3 := mul_le_mul hFM hsle hs0.le hM
          _ = 3 * M := by ring
  rcases key with h | h | h <;> linarith

/-- **I1 (the paraboloid measure is good).**

Proof: finiteness (bounded density with compact support, then `Measure.map`); `μ Sᶜ = 0` (`S` is
compact, hence measurable, and `graphPt⁻¹ Sᶜ ⊆ (closedBall 0 (5/4))ᶜ` where `w = 0`);
`S ⊆ B(0, 3/2)` (`‖graphPt v‖² = ‖v‖² + ‖v‖⁴/4 ≤ 2225/1024`); Frostman with `C = vol B_m(0,1)`:
`‖graphPt v - η‖ ≥ ‖v - horiz η‖`, `w ≤ 1`, so `μ(B(η, r)) ≤ vol B_m(horiz η, r) = C r^m`;
decay with `c = 1/2` from `parab_decay_vert`, `parab_decay_horiz` and `‖μ̂‖ ≤ μ(univ)`
(if `4|xₙ| ≤ ‖x̲‖` then `‖x‖ ≤ 2‖x̲‖`, else `‖x‖ ≤ 5|xₙ|`). -/
theorem goodMeasure_parab (m : ℕ) (hm : 1 ≤ m) : GoodMeasure (parabMeasure m) (parabSet m) where
  finite := isFinite_parab
  null_compl := parab_null_compl
  subset := parabSet_subset
  frostman := parab_frostman hm
  decay := parab_decay hm

/-! ## `parabolic_of_restrMu` -/

theorem continuous_fourier_schwartz {n : ℕ} (f : 𝓢(E n, ℂ)) : Continuous (𝓕 (f : E n → ℂ)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simpa using (continuous_inner : Continuous fun p : E n × E n => ⟪p.1, p.2⟫)) f.integrable

theorem continuous_pr (f : 𝓢(E (m + 1), ℂ)) :
    Continuous (paraboloidRestriction (f : E (m + 1) → ℂ)) :=
  (continuous_fourier_schwartz f).comp continuous_graphPt

theorem restrict_le_dens : (volume : Measure (E m)).restrict (closedBall 0 1) ≤
    volume.withDensity fun v => ENNReal.ofReal (wt m v) := by
  rw [← withDensity_indicator_one measurableSet_closedBall]
  refine withDensity_mono (ae_of_all _ fun v => ?_)
  by_cases hv : v ∈ closedBall (0 : E m) 1
  · rw [indicator_of_mem hv, Pi.one_apply]
    have : wt m v = 1 := (wBump m).one_of_mem_closedBall hv
    simp only [this, ENNReal.ofReal_one, le_refl]
  · rw [indicator_of_notMem hv]
    exact zero_le

theorem pr_le (f : 𝓢(E (m + 1), ℂ)) (q : ℝ) :
    eLpNorm (paraboloidRestriction (f : E (m + 1) → ℂ)) (ENNReal.ofReal q)
        (volume.restrict (closedBall (0 : E m) 1)) ≤
      eLpNorm (𝓕 (f : E (m + 1) → ℂ)) (ENNReal.ofReal q) (parabMeasure m) := by
  unfold parabMeasure
  rw [eLpNorm_map_measure (continuous_fourier_schwartz f).aestronglyMeasurable
    measurable_graphPt.aemeasurable]
  exact eLpNorm_mono_measure _ restrict_le_dens

/-- The cutoff `χ_k`: `1` on `closedBall 0 (k+1)`, supported in `closedBall 0 (2(k+1))`. -/
noncomputable def cut (m k : ℕ) : ContDiffBump (0 : E (m + 1)) :=
  ⟨(k : ℝ) + 1, 2 * ((k : ℝ) + 1), by positivity, by linarith⟩

theorem cutC_hasCompactSupport (k : ℕ) :
    HasCompactSupport fun x : E (m + 1) => ((cut m k x : ℝ) : ℂ) :=
  (cut m k).hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero

/-- `f_k = χ_k f`. -/
noncomputable def fk (f : 𝓢(E (m + 1), ℂ)) (k : ℕ) : 𝓢(E (m + 1), ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun x => ((cut m k x : ℝ) : ℂ) * f x)
    ((cutC_hasCompactSupport k).mul_right)
    ((Complex.ofRealCLM.contDiff.comp (cut m k).contDiff).mul (f.smooth ⊤))

theorem fk_apply (f : 𝓢(E (m + 1), ℂ)) (k : ℕ) (x : E (m + 1)) :
    fk f k x = ((cut m k x : ℝ) : ℂ) * f x := rfl

theorem tsupport_fk (f : 𝓢(E (m + 1), ℂ)) (k : ℕ) :
    tsupport (fk f k : E (m + 1) → ℂ) ⊆ closedBall 0 (2 * ((k : ℝ) + 1)) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  rw [Function.mem_support, fk_apply] at hx
  have h1 : cut m k x ≠ 0 := fun h => hx (by simp [h])
  have h2 : x ∈ Function.support (cut m k) := h1
  rw [(cut m k).support_eq] at h2
  exact ball_subset_closedBall h2

theorem norm_fk_le (f : 𝓢(E (m + 1), ℂ)) (k : ℕ) (x : E (m + 1)) : ‖fk f k x‖ ≤ ‖f x‖ := by
  rw [fk_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (cut m k).nonneg]
  exact mul_le_of_le_one_left (norm_nonneg _) (cut m k).le_one

theorem fk_eventually (f : 𝓢(E (m + 1), ℂ)) (x : E (m + 1)) :
    ∀ᶠ k in atTop, fk f k x = f x := by
  filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with k hk
  have h1 : ‖x‖ ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hx : x ∈ closedBall (0 : E (m + 1)) (cut m k).rIn := by
    rw [mem_closedBall, dist_zero_right]
    change ‖x‖ ≤ (k : ℝ) + 1
    linarith
  rw [fk_apply, (cut m k).one_of_mem_closedBall hx]
  simp

theorem tendsto_fourier_fk (f : 𝓢(E (m + 1), ℂ)) (ξ : E (m + 1)) :
    Tendsto (fun k => 𝓕 (fk f k : E (m + 1) → ℂ) ξ) atTop (𝓝 (𝓕 (f : E (m + 1) → ℂ) ξ)) := by
  simp only [Real.fourier_eq]
  refine tendsto_integral_of_dominated_convergence (fun v => ‖f v‖) (fun k => ?_)
    f.integrable.norm (fun k => ae_of_all _ fun v => ?_) (ae_of_all _ fun v => ?_)
  · exact (Continuous.smul (by fun_prop) (fk f k).continuous).aestronglyMeasurable
  · rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
    exact norm_fk_le f k v
  · exact tendsto_const_nhds.congr' ((fk_eventually f v).mono fun k hk => by simp only [hk])

/-- **F1 (from `R_μ(q, 0)` to Conjecture 4.4's norm).**

Proof: for `f` supported in `B(0, R)`:
`‖f̂ ∘ graphPt‖^q_{Lq(B(0,1))} ≤ ∫ w |f̂ ∘ graphPt|^q = ‖f̂‖^q_{Lq(μ)}` (`w = 1` on the closed unit
ball; `lintegral_map`, `lintegral_withDensity_eq_lintegral_mul`). General Schwartz `f`: let
`f_k = f · χ(·/k)` with `χ` a smooth bump, `0 ≤ χ ≤ 1`, `χ = 1` on `B(0, 1)` (Schwartz by
`HasCompactSupport.toSchwartzMap`); `‖f_k‖_q ≤ ‖f‖_q` pointwise, `‖f_k - f‖₁ → 0` by dominated
convergence, so `f̂_k → f̂` uniformly and the `Lq(B(0,1))` norms converge (finite measure), or use
Fatou. -/
theorem parabolic_of_restrMu (m : ℕ) {q : ℝ} (hq : 1 ≤ q) (h : RestrMu (parabMeasure m) q 0) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(E (m + 1), ℂ),
      eLpNorm (paraboloidRestriction (f : E (m + 1) → ℂ)) (ENNReal.ofReal q)
          (volume.restrict (closedBall (0 : E m) 1)) ≤
        C * eLpNorm f (ENNReal.ofReal q) volume := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun f => ?_⟩
  have hk : ∀ k : ℕ, eLpNorm (paraboloidRestriction (fk f k : E (m + 1) → ℂ)) (ENNReal.ofReal q)
      (volume.restrict (closedBall (0 : E m) 1)) ≤ C * eLpNorm f (ENNReal.ofReal q) volume := by
    intro k
    calc _ ≤ eLpNorm (𝓕 (fk f k : E (m + 1) → ℂ)) (ENNReal.ofReal q) (parabMeasure m) :=
          pr_le _ q
      _ ≤ C * ENNReal.ofReal ((2 * ((k : ℝ) + 1)) ^ (0 : ℝ)) *
            eLpNorm (fk f k) (ENNReal.ofReal q) volume :=
          hC _ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) _ (tsupport_fk f k)
      _ ≤ C * eLpNorm f (ENNReal.ofReal q) volume := by
          rw [Real.rpow_zero, ENNReal.ofReal_one, mul_one]
          gcongr 1
          exact eLpNorm_mono (norm_fk_le f k)
  calc _ ≤ atTop.liminf fun k => eLpNorm (paraboloidRestriction (fk f k : E (m + 1) → ℂ))
          (ENNReal.ofReal q) (volume.restrict (closedBall (0 : E m) 1)) :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun k => (continuous_pr (fk f k)).aestronglyMeasurable)
          _ (ae_of_all _ fun u => tendsto_fourier_fk f _)
    _ ≤ atTop.liminf fun _ : ℕ => C * eLpNorm f (ENNReal.ofReal q) volume :=
        liminf_le_liminf (Eventually.of_forall hk)
    _ = _ := liminf_const _

end TaoBR.Parab.PartI

end S_PartI

namespace TaoBR.Parab
alias goodMeasure_parab := TaoBR.Parab.PartI.goodMeasure_parab
alias parabolic_of_restrMu := TaoBR.Parab.PartI.parabolic_of_restrMu
alias exists_good_exponent := TaoBR.Parab.PartI.exists_good_exponent
end TaoBR.Parab

section S_Target

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace

namespace TaoBR

open Parab

/-- **Target** (Tao, pp. 10–11), proved from the stubs. -/
theorem Parab.target_proof (m : ℕ) (hm : 1 ≤ m) :
    RestrictionConjecture (m + 1) → ParabolicRestrictionConjecture m := by
  intro hRC p hp hpc
  have hptop : p ≠ ⊤ := ne_top_of_lt hpc
  set q := p.toReal with hqdef
  have hq1 : 1 ≤ q := by
    have := ENNReal.toReal_mono hptop hp
    simpa using this
  have hqc : q < 2 * ((m : ℝ) + 1) / ((m : ℝ) + 2) :=
    (ENNReal.lt_ofReal_iff_toReal_lt hptop).mp hpc
  have hμ := goodMeasure_parab m hm
  obtain ⟨κ, α₀, hα₀, hT⟩ := restrMu_zero_of_thick (by omega : 2 ≤ m + 1) hμ
  obtain ⟨p₁, hp₁, hp₁2, hp₁c, hαpos, hαlt, hkey⟩ := exists_good_exponent m hm κ α₀ hα₀ hq1 hqc
  have hcast : (2 * ((m + 1 : ℕ) : ℝ) / (((m + 1 : ℕ) : ℝ) + 1)) =
      2 * ((m : ℝ) + 1) / ((m : ℝ) + 2) := by
    push_cast; ring
  have hR : Restr (m + 1) (ENNReal.ofReal p₁) 0 := by
    refine hRC _ (by rw [ENNReal.one_le_ofReal]; linarith) ?_
    rw [hcast]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hp₁c
  have hthick := thick_of_annulus m hp₁.le (annulus_of_restr (by omega) hp₁.le hR)
  have hR0 := hT p₁ hp₁ hp₁2 _ hαpos hαlt hthick q hq1 hkey
  obtain ⟨C, hC⟩ := parabolic_of_restrMu m hq1 hR0
  refine ⟨C, fun f => ?_⟩
  have := hC f
  rwa [hqdef, ENNReal.ofReal_toReal hptop] at this

end TaoBR

end S_Target

theorem solution (m : ℕ) (hm : 1 ≤ m) :
    TaoBR.RestrictionConjecture (m + 1) → TaoBR.ParabolicRestrictionConjecture m :=
  TaoBR.Parab.target_proof m hm

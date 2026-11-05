-- Prove2me | solution 1 for TaoBR.parabolicRestrictionConjecture_iff_parabolicBochnerRieszConjecture
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T19:44:59.316569+00:00
-- url     : https://prove2.me/submissions/7e33d0f4-0fa5-44a2-8654-bee6c218765f

import Mathlib
import Definitions.Def_TaoBR
import Theorems.Thm_TaoBR_exists_sparse_cover
import Theorems.Thm_TaoBR_opNorm_le_of_contDiff
import Theorems.Thm_TaoBR_parabolicBochnerRieszConjecture_of_parabolicRestrictionConjecture

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
  HasCompactSupport.comp_left (g := Complex.ofReal) (f := (bump n).normed volume)
    (bump n).hasCompactSupport_normed Complex.ofReal_zero

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
  have := (phiS n).integrable_pow_mul volume 1
  simp only [pow_one] at this
  exact this

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
  rw [integral_const_mul, hcv, Complex.real_smul, abs_of_pos (inv_pos.2 (pow_pos hR _))]
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_pos hR _).ne',
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
  exact this.trans_eq (one_mul _)

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
    · simp only [Function.uncurry, norm_mul, Circle.norm_coe, mul_one, one_mul]
      exact (mul_comm _ _).le
  rw [integral_integral_swap hint]
  congr 1; ext y
  rw [integral_mul_const, integral_const_mul]; rfl

lemma Fop_offdiag (hR : 0 < R) (c c' : E n) {G G' : E n → ℂ} (hG : Integrable G)
    (hG' : Integrable G') (hGm : StronglyMeasurable G) (hGm' : StronglyMeasurable G') :
    ‖∫ ω, Fop n R c G ω * conj (Fop n R c' G' ω) ∂(μ)‖ₑ ≤
      (∫⁻ η, ‖G η‖ₑ) * (∫⁻ η, ‖G' η‖ₑ) *
        ∫⁻ y, ∫⁻ y', ‖phiLoc n R c y‖ₑ * ‖phiLoc n R c' y'‖ₑ * ‖ftMeasure μ (y - y')‖ₑ := by
  have _hsf : SFinite (volume : Measure (E n)) := inferInstance
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
    · simp only [Function.uncurry, norm_mul, RCLike.norm_conj, Circle.norm_coe, mul_one, one_mul,
        norm_norm, le_refl]
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
            ≤ ‖phiLoc n R c p.1‖ₑ * A * (‖phiLoc n R c' p.2‖ₑ * A') * ‖ftMeasure μ (p.1 - p.2)‖ₑ :=
              mul_le_mul_left (mul_le_mul' (mul_le_mul_right e1 _) (mul_le_mul_right e2 _)) _
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
        ← ENNReal.ofReal_mul hT,
        ← ENNReal.ofReal_add hB (mul_nonneg hT (add_nonneg (norm_nonneg _) (norm_nonneg _)))]
      exact ENNReal.ofReal_le_ofReal (hpt y y')
    calc a y * a' y' * ‖ftMeasure μ (y - y')‖ₑ
        ≤ a y * a' y' * (β + τ * (ENNReal.ofReal ‖y - c‖ + ENNReal.ofReal ‖y' - c'‖)) :=
          mul_le_mul_right h1 _
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
        have hX : 0 ≤ R ^ n * M0 n := mul_nonneg (pow_nonneg hR.le _) h0
        have hY : 0 ≤ R ^ (n + 1) * M1 n := mul_nonneg (pow_nonneg hR.le _) h1
        rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_mul (mul_nonneg hB hX),
          ← ENNReal.ofReal_mul hT, ← ENNReal.ofReal_mul (mul_nonneg hT hY),
          ← ENNReal.ofReal_mul hT, ← ENNReal.ofReal_mul (mul_nonneg hT hX),
          ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hT hY) hX) (mul_nonneg (mul_nonneg hT hX) hY),
          ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hB hX) hX)
            (add_nonneg (mul_nonneg (mul_nonneg hT hY) hX) (mul_nonneg (mul_nonneg hT hX) hY))]
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
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le two_pos hw2
  have hd0 : 0 ≤ d := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hD1 : 1 ≤ D := le_max_left _ _
  have hDQ : 0 ≤ D / Q := div_nonneg (zero_le_one.trans hD1) (zero_le_one.trans hQ)
  have hsig := sig_norm_le (μ := μ) (y - y')
  by_cases hd : d * 2 ≤ ‖w‖
  · have hz : ‖w‖ / 2 ≤ ‖y - y'‖ := by
      have e : y - y' = w + (y - c) - (y' - c') := by simp only [w]; abel
      have := norm_sub_norm_le w (-(y - c) + (y' - c'))
      have h2 : ‖-(y - c) + (y' - c')‖ ≤ d := (norm_add_le _ _).trans (by rw [norm_neg])
      have e2 : w - (-(y - c) + (y' - c')) = y - y' := by rw [e]; abel
      rw [e2] at this
      linarith only [this, h2, hd]
    have hz1 : 1 ≤ ‖y - y'‖ := by linarith only [hw2, hz]
    have hk := hdec (y - y') hz1
    set a := ‖ftMeasure μ (y - y')‖
    have ha : 0 ≤ a := norm_nonneg _
    have hCs : 0 ≤ Cs := le_trans (mul_nonneg (pow_nonneg ha _) (norm_nonneg _)) hk
    have h1 : a ^ m * ‖w‖ ≤ 2 * Cs := by
      have : a ^ m * (‖w‖ / 2) ≤ Cs :=
        le_trans (mul_le_mul_of_nonneg_left hz (pow_nonneg ha _)) hk
      linarith only [this]
    have h2 : (a * Q) ^ m ≤ D ^ m := by
      rw [mul_pow]
      calc a ^ m * Q ^ m ≤ a ^ m * ‖w‖ := mul_le_mul_of_nonneg_left hQw (pow_nonneg ha _)
        _ ≤ 2 * Cs := h1
        _ ≤ D := le_max_right _ _
        _ ≤ D ^ m := le_self_pow₀ hD1 hm.ne'
    have h3 : a * Q ≤ D :=
      (pow_le_pow_iff_left₀ (mul_nonneg ha (zero_le_one.trans hQ)) (zero_le_one.trans hD1) hm.ne').1 h2
    have h4 : a ≤ D / Q := by rw [le_div_iff₀ (zero_lt_one.trans_le hQ)]; exact h3
    have : 0 ≤ 4 * s / ‖w‖ * d := mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hs) hw0.le) hd0
    linarith only [h4, this]
  · rw [not_le] at hd
    have : s ≤ 4 * s / ‖w‖ * d := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hw0]
      have := mul_le_mul_of_nonneg_left hd.le hs
      linarith only [this, mul_nonneg hs hd0]
    linarith only [hsig, this, hDQ]

variable {N : ℕ} {x : Fin N → E n}

lemma Fop_diag (hR : 1 ≤ R) (c : E n) {A1 : ℝ}
    (hcap : ∀ η : E n, ∫⁻ ω, ‖Kker n R c (ω - η)‖ₑ ∂μ ≤ ENNReal.ofReal (A1 * R))
    {G : E n → ℂ} (hGm : Measurable G) :
    ∫⁻ ω, ‖Fop n R c G ω‖ₑ ^ 2 ∂(μ) ≤
      ENNReal.ofReal (A1 * R) * ∫⁻ η, ‖G η‖ₑ ^ 2 := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
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
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set X := R * (N : ℝ) with hX
  have hX2 : 2 ≤ X := (one_mul (2 : ℝ)).symm.le.trans (mul_le_mul hR hN2 zero_le_two hR0.le)
  have hX1 : 1 ≤ X := one_le_two.trans hX2
  set C0 := 2 * n * m + 3 * n + 3
  set w := c - c'
  set Q := R ^ (2 * n) * (N : ℝ) with hQ
  have hQ1 : 1 ≤ Q := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR) hN1
  have hw2 : 2 ≤ ‖w‖ := le_trans (le_trans hX2 (le_self_pow₀ hX1 (by omega))) hw
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le two_pos hw2
  have hQw : Q ^ m ≤ ‖w‖ := by
    calc Q ^ m = R ^ (2 * n * m) * (N : ℝ) ^ m := by rw [hQ, mul_pow, ← pow_mul]
      _ ≤ R ^ (2 * n * m) * (N : ℝ) ^ (2 * n * m) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN1 (Nat.le_mul_of_pos_left m (by omega)))
            (pow_nonneg hR0.le _)
      _ = X ^ (2 * n * m) := by rw [hX, mul_pow]
      _ ≤ X ^ C0 := pow_le_pow_right₀ hX1 (by omega)
      _ ≤ ‖w‖ := hw
  have hRw : R ^ (2 * n + 1) * N ≤ ‖w‖ := by
    calc R ^ (2 * n + 1) * (N : ℝ) ≤ R ^ (2 * n + 1) * (N : ℝ) ^ (2 * n + 1) :=
          mul_le_mul_of_nonneg_left (le_self_pow₀ hN1 (by omega)) (pow_nonneg hR0.le _)
      _ = X ^ (2 * n + 1) := by rw [hX, mul_pow]
      _ ≤ X ^ C0 := pow_le_pow_right₀ hX1 (by omega)
      _ ≤ ‖w‖ := hw
  set D := max 1 (2 * Cs)
  set s := (μ).real univ
  have hs : 0 ≤ s := measureReal_nonneg
  have hD : 0 ≤ D := le_trans zero_le_one (le_max_left _ _)
  have hk := kern_le hR0 c c' (D / Q) (4 * s / ‖w‖) (div_nonneg hD (zero_le_one.trans hQ1))
    (div_nonneg (mul_nonneg (by norm_num) hs) hw0.le)
    (sig_pt m hm Cs hdec c c' Q hQ1 hw2 hQw)
  refine hk.trans (ENNReal.ofReal_le_ofReal ?_)
  have h0 := M0_nonneg (n := n)
  have h1 := M1_nonneg (n := n)
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le two_pos hN2
  have t1 : D / Q * (R ^ n * M0 n) ^ 2 = D * M0 n ^ 2 / N := by
    rw [hQ, mul_pow, ← pow_mul]; field_simp; ring
  have t2 : 4 * s / ‖w‖ * (2 * R ^ (2 * n + 1) * M0 n * M1 n) ≤
      8 * s * M0 n * M1 n / N := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hw0 hN0]
    have := mul_le_mul_of_nonneg_left hRw
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) h0) h1 : 0 ≤ 8 * s * M0 n * M1 n)
    linarith only [this]
  rw [t1, Cst, add_div]
  exact add_le_add_right t2 _

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
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
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
    · exact Eventually.of_forall (fun ω => by simp only [Pi.zero_apply]; rw [← hsq]; exact sq_nonneg _)
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
      (Eventually.of_forall (fun _ => sq_nonneg _))
      ((hFm i).measurable.norm.pow_const 2).aestronglyMeasurable]
    have e2 : ∀ ω, ENNReal.ofReal (‖F i ω‖ ^ 2) = ‖F i ω‖ₑ ^ 2 := by
      intro ω; rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    simp_rw [e2]
    have hd := Fop_diag hR (x i) (hcap (x i)) (hGs i).measurable
    rw [hB i, ← ENNReal.ofReal_mul (mul_nonneg hA1 hR0.le)] at hd
    calc _ ≤ (ENNReal.ofReal (A1 * R * b i)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
      _ = _ := ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hA1 hR0.le) (hb0 i))
  have hC := Cst_nonneg μ Cs
  have hoff : ∀ i j, i ≠ j →
      (∫ ω, F i ω * conj (F j ω) ∂σ).re ≤ Cst μ Cs / N * (a i * a j) := by
    intro i j hij
    have hN : 2 ≤ N := by
      have := i.2; have := j.2; have : (i : ℕ) ≠ j := Fin.val_ne_of_ne hij; omega
    have hk := kern_sparse hn m hm Cs hdec hR N hN (x i) (x j) (hsp i j hij)
    have ho := Fop_offdiag (μ := μ) hR0 (x i) (x j) (hGi i) (hGi j) (hGs i) (hGs j)
    rw [hA, hA] at ho
    have h2 := ho.trans (mul_le_mul_of_nonneg_left hk zero_le)
    have hai := ha0 i
    have haj := ha0 j
    have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [← ENNReal.ofReal_mul hai, ← ENNReal.ofReal_mul (mul_nonneg hai haj), ← ofReal_norm] at h2
    have h3 := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg hai haj) (div_nonneg hC hNn))).1 h2
    calc _ ≤ ‖∫ ω, F i ω * conj (F j ω) ∂σ‖ := Complex.re_le_norm _
      _ ≤ _ := h3.trans (le_of_eq (by ring))
  have hsum : ∑ i, ∑ j, (∫ ω, F i ω * conj (F j ω) ∂σ).re ≤
      ∑ i, ∑ j, ((if i = j then A1 * R * b i else 0) + Cst μ Cs / N * (a i * a j)) := by
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      exact le_add_of_le_of_nonneg (hdiag i)
        (mul_nonneg (div_nonneg hC (Nat.cast_nonneg N)) (mul_self_nonneg _))
    · simp only [hij, if_false, zero_add]
      exact hoff i j hij
  have hcomb : ∑ i, ∑ j, ((if i = j then A1 * R * b i else 0) + Cst μ Cs / N * (a i * a j)) =
      A1 * R * ∑ i, b i + Cst μ Cs / N * (∑ i, a i) ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.mul_sum, sq, Finset.sum_mul_sum]
  have hCS : Cst μ Cs / N * (∑ i, a i) ^ 2 ≤ Cst μ Cs * V * ∑ i, b i := by
    have h1 : (∑ i, a i) ^ 2 ≤ N * ∑ i, a i ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
      rwa [Finset.card_univ, Fintype.card_fin] at h
    have h2 : ∑ i, a i ^ 2 ≤ V * ∑ i, b i := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun i _ => hab i)
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_mul_eq_mul_div, div_le_iff₀ hN0]
      calc Cst μ Cs * (∑ i, a i) ^ 2 ≤ Cst μ Cs * (N * (V * ∑ i, b i)) := by
            exact mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hN0.le)) hC
        _ = _ := by ring
  have hbn : 0 ≤ ∑ i, b i := Finset.sum_nonneg (fun i _ => hb0 i)
  rw [hLHS]
  calc ENNReal.ofReal (∑ i, ∑ j, (∫ ω, F i ω * conj (F j ω) ∂σ).re)
      ≤ ENNReal.ofReal ((A1 + Cst μ Cs * V) * R * ∑ i, b i) := by
        apply ENNReal.ofReal_le_ofReal
        have hcv : 0 ≤ Cst μ Cs * V * ∑ i, b i := mul_nonneg (mul_nonneg hC hV) hbn
        have h4 := mul_le_mul_of_nonneg_right hR hcv
        linarith only [hsum, hcomb, hCS, h4]
    _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg (add_nonneg hA1 (mul_nonneg hC hV)) hR0.le),
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
    · simp only [a, indicator_of_mem h, Pi.one_apply, one_mul]
    · simp only [hg η h, enorm_zero, mul_zero]
  have hb : ∀ η, a η * ‖g η‖ₑ ^ 2 ≤ ‖g η‖ₑ ^ 2 := by
    intro η
    by_cases h : η ∈ closedBall (0 : E n) 2
    · simp only [a, indicator_of_mem h, Pi.one_apply, one_mul, le_refl]
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
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
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
  have hr0 : 0 < r := one_div_pos.2 (mul_pos (by norm_num) hR0)
  have hc : μ (ball η r) ≤ ENNReal.ofReal (max CF 0 * r ^ (n - 1)) :=
    (hF η r hr0).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hr0.le _)))
  calc ENNReal.ofReal (R ^ n * MPhi n) * μ (ball η r)
      ≤ ENNReal.ofReal (R ^ n * MPhi n) * ENNReal.ofReal (max CF 0 * r ^ (n - 1)) :=
        mul_le_mul_right hc _
    _ = ENNReal.ofReal (A1 n CF * R) := ?_
  rw [← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hR0.le _) (MPhi_nonneg n))]
  congr 1
  simp only [A1, r]
  have hn1 : R ^ n = R * R ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  rw [hn1, div_pow, mul_pow, one_pow, div_pow, one_pow]
  have : R ^ (n - 1) ≠ 0 := pow_ne_zero _ hR0.ne'
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
  have hk0 : 0 < k := Nat.ceil_pos.2 (one_div_pos.2 hc)
  have hkc : 1 ≤ c * k := by
    have := Nat.le_ceil (1 / c)
    rw [← hk] at this
    rw [div_le_iff₀ hc] at this
    exact this.trans_eq (mul_comm _ _)
  refine ⟨k, hk0, C ^ k, fun z hz => ?_⟩
  set t := ‖z‖
  have ht : 0 ≤ t := norm_nonneg _
  have h1t : 1 ≤ 1 + t := le_add_of_nonneg_right ht
  have hb : 0 ≤ (1 + t) ^ (-c) := Real.rpow_nonneg (zero_le_one.trans h1t) _
  have h1 : ‖f z‖ ^ k ≤ C ^ k * (1 + t)⁻¹ := by
    calc ‖f z‖ ^ k ≤ (C * (1 + t) ^ (-c)) ^ k := pow_le_pow_left₀ (norm_nonneg _) (h z) k
      _ = C ^ k * (1 + t) ^ (-c * k) := by
          rw [mul_pow, Real.rpow_mul_natCast (zero_le_one.trans h1t)]
      _ ≤ C ^ k * (1 + t) ^ (-1 : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le h1t (by linarith only [hkc])) (pow_nonneg hC _)
      _ = C ^ k * (1 + t)⁻¹ := by rw [Real.rpow_neg_one]
  have hCk : 0 ≤ C ^ k := pow_nonneg hC _
  calc ‖f z‖ ^ k * t ≤ C ^ k * (1 + t)⁻¹ * t := mul_le_mul_of_nonneg_right h1 ht
    _ = C ^ k * (t / (1 + t)) := by ring
    _ ≤ C ^ k * 1 :=
        mul_le_mul_of_nonneg_left
          ((div_le_one (lt_of_lt_of_le one_pos h1t)).2 (le_add_of_nonneg_left zero_le_one)) hCk
    _ = C ^ k := mul_one _

/-! ## Restriction to `B(0, 2)` and the main bound -/

omit [IsFiniteMeasure μ] in
lemma Top_eq_restrict (hR : 1 ≤ R) (G : Fin N → E n → ℂ) (hG : ∀ i, Integrable (G i))
    {ω : E n} (hω : ‖ω‖ ≤ 3 / 2) :
    Top R x G ω = Top R x (fun i => (closedBall (0 : E n) 2).indicator
      ((hG i).aestronglyMeasurable.mk (G i))) ω := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  unfold Top
  refine Finset.sum_congr rfl (fun i _ => integral_congr_ae ?_)
  filter_upwards [(hG i).aestronglyMeasurable.ae_eq_mk] with η hη
  by_cases hK : Kker n R (x i) (ω - η) = 0
  · simp [hK]
  · have h1 := K_support hR0 hK
    have h2 : 1 / (16 * R) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hR0) (by norm_num)]; linarith only [hR]
    have hmem : η ∈ closedBall (0 : E n) 2 := by
      rw [mem_closedBall_zero_iff]
      have := norm_sub_le ω (ω - η)
      rw [sub_sub_cancel] at this
      linarith only [this, h1, h2, hω]
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
    add_nonneg (A1_nonneg n CF) (mul_nonneg (Cst_nonneg μ Cs) hV), ?_⟩
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
    · simp only [G', indicator_of_notMem h, enorm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_le]
  have hfin : ∀ i, ∫⁻ η, ‖G i η‖ₑ ^ 2 ≠ ⊤ := by
    intro i
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
      (hGL2 i).eLpNorm_lt_top
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at this
    exact this.ne
  have hL1 : ∀ i, (∫⁻ η, ‖G' i η‖ₑ) ^ 2 ≤ ENNReal.ofReal V * ∫⁻ η, ‖G' i η‖ₑ ^ 2 := by
    intro i
    exact l1_l2_ball (G' i) (hGs' i).measurable (fun η h => indicator_of_notMem h _)
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


export TaoBR.Parab.PartA (PhiC MPhi Phi_nonneg Phi_le MPhi_nonneg Phi_support Phi_integral PhiC_contDiff PhiC_hasCompactSupport PhiS phiS phi phi_eq phiLoc K_support K_norm_le K_continuous K_integrable phiLoc_contDiff)













lemma Phi_integrable (n : ℕ) : Integrable (Phi n) := (bump n).integrable_normed

variable {n : ℕ} {R : ℝ} {c : E n}





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
          exact (mul_le_mul hv.le hy.le (norm_nonneg _) (by norm_num)).trans (le_of_eq (by norm_num))
        have h2 := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * ⟪v, y⟫)
        have h3 : (2 * Real.pi * ⟪v, y⟫) ^ 2 ≤ 1 := by
          rw [mul_pow]
          have : ⟪v, y⟫ ^ 2 ≤ (1 / 8) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
          have hpi : (2 * Real.pi) ^ 2 ≤ 64 :=
            (pow_le_pow_left₀ (mul_nonneg zero_le_two Real.pi_pos.le)
              (show 2 * Real.pi ≤ 8 by linarith only [Real.pi_lt_four]) 2).trans
              (le_of_eq (by norm_num))
          exact (mul_le_mul hpi this (sq_nonneg _) (by norm_num)).trans (le_of_eq (by norm_num))
        linarith only [h2, h3]
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
  have : 8 * R ≤ R ^ (3 * n + 3) * (N : ℝ) ^ (3 * n + 3) := by
    rw [mul_comm]
    exact mul_le_mul h1 h2 (by norm_num) (pow_nonneg (zero_le_one.trans hR) _)
  linarith only [this, h]

/-- The pieces `g_i = f / φ_i` near `x_i`. -/
noncomputable def gfun (n : ℕ) (R : ℝ) (c : E n) (f : E n → ℂ) (y : E n) : ℂ :=
  if dist y c < 2 * R then f y / phiLoc n R c y else 0

lemma decomp (n : ℕ) (hn : 2 ≤ n) {R : ℝ} (hR : 1 ≤ R) {N : ℕ} (x : Fin N → E n)
    (hx : IsSparse ((3 * n + 3 : ℕ) : ℝ) R x) (f : 𝓢(E n, ℂ))
    (hf : tsupport f ⊆ ⋃ i, closedBall (x i) R) {q : ℝ} (hq : 0 < q) :
    ∃ g : Fin N → 𝓢(E n, ℂ), (∀ i, tsupport (g i) ⊆ closedBall (x i) R) ∧
      (∀ y, f y = ∑ i, g i y * phiLoc n R (x i) y) ∧
      ∑ i, ∫⁻ y, ‖g i y‖ₑ ^ q ≤ (2 : ℝ≥0∞) ^ q * ∫⁻ y, ‖f y‖ₑ ^ q := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
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
    have h1 := sparse_far hR hx hij
    have h2 := dist_triangle (x i) y (x j)
    rw [dist_comm (x i) y] at h2
    linarith only [h1, h2, hi, hR0]
  have hzero : ∀ i y, R < dist y (x i) → gfun n R (x i) f y = 0 := by
    intro i y hy
    unfold gfun
    split_ifs with h
    · rw [hf0 y (fun j => ?_), zero_div]
      by_cases hij : i = j
      · subst hij; exact hy
      · linarith only [huniq y i j h hij, hR0]
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
    · have hy' : R < dist y (x i) := by linarith only [not_lt.1 hy, hR0]
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
      rw [hf0 y (fun i => by linarith only [h i, hR0])]
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
            rw [div_le_iff₀ (one_half_pos.trans_le hl)]
            exact (le_of_eq (by ring)).trans
              (mul_le_mul_of_nonneg_left hl (mul_nonneg zero_le_two (norm_nonneg (f y))))
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
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [hR]
  rw [mem_closedBall]
  linarith only [dist_triangle η z 0, h1, h2, hd]

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
  have hq0 : 0 < p := zero_lt_one.trans hp
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
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  obtain ⟨g, hgs, hfg, hgsum⟩ := decomp n hn hR x (isSparse_mono hR hC0 hx) f hf hq0
  set G : Fin N → E n → ℂ := fun i => (Th S R).indicator (𝓕 (g i : E n → ℂ)) with hG_def
  have hPG : PG S R G := PG_G hR g
  have hSub := hμ.subset
  have hmarc := marc (volume : Measure (E n)) μ (PG S R) (Top R x)
    (ENNReal.ofReal (A * R)) (fun G t hG => PG_truncHi hG t) (fun G t hG => PG_truncLo hG t)
    (fun G G' hG hG' => Top_add hR0 G G' (PG_integrable hSub hR hG) (PG_integrable hSub hR hG'))
    (fun G hG => Top_meas G (fun i => (hG i).1)) (fun G hG i => (hG i).1)
    (fun G hG => (Top_L1 (by omega) hR hF G (fun i => (hG i).1)).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right hA2 : A1 n CF ≤ A) hR0.le)) _))
    (fun G hG => (hL2 R hR N x hx G (PG_integrable hSub hR hG) (PG_memLp hSub hR hG)).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hA1 : A2 ≤ A) hR0.le)) _))
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
          rw [← ENNReal.ofReal_mul (show 0 ≤ A * R from mul_nonneg (add_nonneg hA1 hA2) hR0.le),
            mul_assoc A, mul_one_div_cancel hR0.ne',
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
  · intro h i
    obtain ⟨h1, h2⟩ := abs_sub_le_iff.1 (h i)
    exact ⟨sub_le_comm.1 h2, sub_le_iff_le_add'.1 h1⟩
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    exact abs_sub_le_iff.2 ⟨sub_le_iff_le_add'.2 h2, sub_le_comm.1 h1⟩

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
  have hone : (1 : ℝ) ≤ |(k i : ℝ) - k' i| := by
    have : k i - k' i ≠ 0 := sub_ne_zero.mpr hi
    have h3 : (1 : ℤ) ≤ |k i - k' i| := Int.one_le_abs this
    exact_mod_cast h3
  have htri : |(k i : ℝ) - k' i| ≤ |x i - k i| + |x i - k' i| := by
    calc |(k i : ℝ) - k' i| = |(x i - k' i) - (x i - k i)| := by ring_nf
      _ ≤ |x i - k' i| + |x i - k i| := abs_sub _ _
      _ = _ := add_comm _ _
  linarith only [hone, htri, h1, h2, hc1]

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
  linarith only [hb]

lemma riemann_sum_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (L : ℕ) (hL : 1 ≤ L) :
    (1 / (L : ℝ)) * ∑ j ∈ Finset.range L, (((j : ℝ) + 1) / L) ^ (-a) ≤ 1 / (1 - a) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hstep : ∀ j ∈ Finset.range L, (1 / (L : ℝ)) * (((j : ℝ) + 1) / L) ^ (-a) ≤
      ((((j : ℝ) + 1) / L) ^ (1 - a) - ((j : ℝ) / L) ^ (1 - a)) / (1 - a) := by
    intro j _
    have := bernoulli_step ha0 ha1 (x := ((j : ℝ) + 1) / L) (h := 1 / L)
      (div_pos (Nat.cast_add_one_pos j) hL') (one_div_nonneg.2 hL'.le)
      (div_le_div_of_nonneg_right (le_add_of_nonneg_left (Nat.cast_nonneg j)) hL'.le)
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
  have hq0 : 0 < q₀ := by linarith only [hq, hqq]
  set a' := q / q₀ with ha'
  have ha0 : 0 ≤ a' := div_nonneg (zero_le_one.trans hq) hq0.le
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
    have hx : 0 < ((j : ℝ) + 1) / L := div_pos (Nat.cast_add_one_pos j) hL'
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
      linarith only [hsum, hsub, hT]
    calc ((t.card : ℝ) * c ^ n) ^ (1 / q₀) ≤ (((((j : ℝ) + 1) / L) ^ q)⁻¹) ^ (1 / q₀) :=
          Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc.le n)) hcheb
            (one_div_nonneg.2 hq0.le)
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
  have hLbig : (s.card : ℝ) * c ^ n ≤ L :=
    (Nat.le_ceil ((s.card : ℝ) * c ^ n)).trans
      (Nat.cast_le.mpr (Nat.le_succ _ : ⌈(s.card : ℝ) * c ^ n⌉₊ ≤ L))
  set u : (Fin n → ℤ) → ℝ := fun k => min (b k) 1
  set a : (Fin n → ℤ) → ℕ := fun k => ⌊(L : ℝ) * u k⌋₊
  have hu0 : ∀ k, 0 ≤ u k := fun k => le_min (hb k) zero_le_one
  have hu1 : ∀ k, u k ≤ 1 := fun k => min_le_right _ _
  have haL : ∀ k ∈ s, a k ≤ L := by
    intro k _
    have : (L : ℝ) * u k ≤ L := mul_le_of_le_one_right (Nat.cast_nonneg _) (hu1 k)
    exact Nat.floor_le_of_le (by exact_mod_cast this) |> fun h => by exact_mod_cast h
  have hab : ∀ k ∈ s, (a k : ℝ) ≤ L * b k := by
    intro k _
    have := Nat.floor_le (mul_nonneg (Nat.cast_nonneg L) (hu0 k))
    have hub : u k ≤ b k := min_le_left _ _
    calc (a k : ℝ) ≤ L * u k := this
      _ ≤ L * b k := mul_le_mul_of_nonneg_left hub (Nat.cast_nonneg _)
  -- the three pieces
  set r : (Fin n → ℤ) → ℝ := fun k => u k - a k * (1 / L)
  set v : (Fin n → ℤ) → ℝ := fun k => b k - u k
  have hdec : (fun k => (b k : ℂ)) =
      fun k => ((a k : ℂ) * (1 / (L : ℂ)) + (r k : ℂ)) + (v k : ℂ) := by
    funext k; simp only [r, v]; push_cast; ring
  have hr : ∀ k, 0 ≤ r k ∧ r k ≤ 1 / L := by
    intro k
    have h1 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg L) (hu0 k))
    have h2 := Nat.lt_floor_add_one ((L : ℝ) * u k)
    simp only [r]
    constructor
    · rw [sub_nonneg, mul_one_div, div_le_iff₀ hL']; linarith only [h1]
    · have e : u k - (a k : ℝ) * (1 / L) = ((L : ℝ) * u k - a k) / L := by
        rw [sub_div, mul_div_cancel_left₀ _ hL'.ne', mul_one_div]
      rw [e, div_le_div_iff_of_pos_right hL']; linarith only [h2]
  have hv : ∀ k, 0 ≤ v k ∧ v k ≤ b k ^ q := by
    intro k
    simp only [v, u]
    constructor
    · exact sub_nonneg.2 (min_le_left _ _)
    · rcases le_total (b k) 1 with h | h
      · rw [min_eq_left h, sub_self]; exact Real.rpow_nonneg (hb k) _
      · rw [min_eq_right h]
        calc b k - 1 ≤ b k := sub_le_self _ zero_le_one
          _ = b k ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ b k ^ q := Real.rpow_le_rpow_of_exponent_le h hq
  rw [hdec, cubeSum_add, cubeSum_add]
  have hbound1 : eLpNorm (cubeSum c s (fun k => (r k : ℂ))) (ENNReal.ofReal q) μ ≤
      μ Set.univ ^ (ENNReal.ofReal q).toReal⁻¹ * ENNReal.ofReal 1 := by
    apply eLpNorm_le_of_bound
    intro ω
    refine (norm_cubeSum_le hc.le s _ ω).trans ?_
    calc ∑ k ∈ s, ‖(r k : ℂ)‖ * c ^ n ≤ ∑ k ∈ s, (1 / (L : ℝ)) * c ^ n :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
            (by rw [Complex.norm_real, Real.norm_of_nonneg (hr k).1]; exact (hr k).2)
            (pow_nonneg hc.le n)
      _ = (s.card : ℝ) * c ^ n / L := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 1 := by rw [div_le_one hL']; exact hLbig
  have hbound2 : eLpNorm (cubeSum c s (fun k => (v k : ℂ))) (ENNReal.ofReal q) μ ≤
      μ Set.univ ^ (ENNReal.ofReal q).toReal⁻¹ * ENNReal.ofReal 1 := by
    apply eLpNorm_le_of_bound
    intro ω
    refine (norm_cubeSum_le hc.le s _ ω).trans ?_
    calc ∑ k ∈ s, ‖(v k : ℂ)‖ * c ^ n ≤ ∑ k ∈ s, b k ^ q * c ^ n :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
            (by rw [Complex.norm_real, Real.norm_of_nonneg (hv k).1]; exact (hv k).2)
            (pow_nonneg hc.le n)
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
  have hq0 : 0 < q := zero_lt_one.trans_le hq
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
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hc.le n)
      rw [Real.div_rpow (le_max_right _ _) hlam0.le, hlamq, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 hT.le)
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
          · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
          · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
        have e2 : max (a k).im 0 / lam - max (-(a k).im) 0 / lam = (a k).im / lam := by
          rw [← sub_div]; congr 1
          rcases le_total 0 (a k).im with h | h
          · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
          · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
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
          refine (eLpNorm_add_le ((a1.add a2).add a3) a4 hq1).trans (add_le_add ?_ le_rfl)
          refine (eLpNorm_add_le (a1.add a2) a3 hq1).trans (add_le_add ?_ le_rfl)
          exact eLpNorm_add_le a1 a2 hq1
      _ = eLpNorm (cubeSum c s (fun k => (b1 k : ℂ))) (ENNReal.ofReal q) μ +
          eLpNorm (cubeSum c s (fun k => (b2 k : ℂ))) (ENNReal.ofReal q) μ +
          eLpNorm (cubeSum c s (fun k => (b3 k : ℂ))) (ENNReal.ofReal q) μ +
          eLpNorm (cubeSum c s (fun k => (b4 k : ℂ))) (ENNReal.ofReal q) μ := by
          rw [hm _ hn1, hm _ hI, hm _ hnI]
      _ ≤ K2 μ q q₀ A + K2 μ q q₀ A + K2 μ q q₀ A + K2 μ q q₀ A :=
          add_le_add (add_le_add (add_le_add B1 B2) B3) B4
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
  have h1 : 1 ≤ ‖phi c 0 (ω : E n)‖ / m := by rw [le_div_iff₀ hm0, one_mul]; exact hph
  exact le_mul_of_one_le_left (norm_nonneg S) h1

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
  have hqr0 : 0 < qr := zero_lt_one.trans_le hqr1
  set σu := μ Set.univ with hσu
  have hσtop : σu ≠ ⊤ := measure_ne_top _ _
  set e := 1 / qr - 1 / p with he
  have he0 : 0 ≤ e := by
    rw [he, sub_nonneg]; exact one_div_le_one_div_of_le hqr0 (hqrq.le.trans hq₀p)
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
      (ENNReal.ofReal_le_ofReal (hqrq.le.trans hq₀p)) (aesm_cubeSum c t (fun _ => 1))
    rw [ENNReal.toReal_ofReal hqr0.le, ENNReal.toReal_ofReal (hqr0.le.trans (hqrq.le.trans hq₀p))] at h2
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
          exact mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc.le n)) _)
      _ = ENNReal.ofReal (A * ((t.card : ℝ) * c ^ n) ^ (1 / q₀)) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg (le_max_right C 0)
            (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc.le n)) _)), hAdef]
          ring_nf
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
  let b : ∀ i, ContDiffBump (x i) := fun i => ⟨R, 2 * R, hR, by linarith only [hR]⟩
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
        exact hj (unique_ball hsep (mem_ball.2 hlt) hi)
      · intro h; exact absurd (Finset.mem_univ i) h
    · push_neg at h
      rw [Finset.sum_eq_zero fun j _ => (b j).zero_of_le_dist (by
        have := h j; rw [mem_ball] at this; push_neg at this; exact this)]
      exact ⟨le_rfl, zero_le_one⟩
  · intro y hy
    dsimp only
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    rw [Finset.sum_eq_single i]
    · exact (b i).one_of_mem_closedBall hi
    · intro j _ hj
      apply (b j).zero_of_le_dist
      by_contra hlt; push_neg at hlt
      have hi' : y ∈ ball (x i) (2 * R) := by
        rw [mem_closedBall] at hi; rw [mem_ball]; linarith only [hi, hR]
      exact hj (unique_ball hsep (mem_ball.2 hlt) hi')
    · intro h; exact absurd (Finset.mem_univ i) h
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
  have hq0 : 0 < q := by linarith only [hq]
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
          linarith only [hε]

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
        linarith only [this]

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

export TaoBR.Parab.PartC (cCube_eq measurableSet_cCube volume_cCube volume_cCube_lt_top)



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
    have hM1 : (1 : ℝ) ≤ M := by linarith only [hM]
    have hRC : 1 ≤ R ^ C := Real.one_le_rpow hR (by linarith only [hC2])
    have hMC : 1 ≤ (M : ℝ) ^ C := Real.one_le_rpow hM1 (by linarith only [hC2])
    have h2M : (2 : ℝ) ^ C ≤ (M : ℝ) ^ C := Real.rpow_le_rpow (by norm_num) hM (by linarith only [hC2])
    calc (2 * R) ^ C * (M : ℝ) ^ C = 2 ^ C * R ^ C * (M : ℝ) ^ C := by
          rw [Real.mul_rpow (by norm_num) (by linarith only [hR])]
      _ ≤ (M : ℝ) ^ C * R ^ C * (M : ℝ) ^ C := by gcongr
      _ = (R ^ C * ((M : ℝ) ^ C * (M : ℝ) ^ C)) * 1 := by ring
      _ ≤ (R ^ C * ((M : ℝ) ^ C * (M : ℝ) ^ C)) * R ^ C :=
          mul_le_mul_of_nonneg_left hRC (by positivity)
      _ = (R ^ C * R ^ C) * ((M : ℝ) ^ C * (M : ℝ) ^ C) := by ring
      _ = R ^ (2 * C) * (M : ℝ) ^ (2 * C) := by
          rw [two_mul, Real.rpow_add (by linarith only [hR]), Real.rpow_add (by linarith only [hM1])]
      _ ≤ dist (x i) (x j) := h i j hij
  constructor
  · intro i j hij
    refine le_trans ?_ (key i j hij)
    have hM1 : (1 : ℝ) ≤ M := by
      have : (1 : ℕ) ≤ M := Nat.one_le_iff_ne_zero.mpr (fun h0 => by subst h0; exact i.elim0)
      exact_mod_cast this
    exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by linarith only [hR]) hC0)
      (Real.rpow_le_rpow_of_exponent_le hM1 hC0) (by positivity) (by positivity)
  · intro i j hij
    refine le_trans ?_ (key i j hij)
    have hM1 : (1 : ℝ) ≤ M := by
      have : (1 : ℕ) ≤ M := Nat.one_le_iff_ne_zero.mpr (fun h0 => by subst h0; exact i.elim0)
      exact_mod_cast this
    have h1 : (2 * R) ^ (2 : ℝ) ≤ (2 * R) ^ C := Real.rpow_le_rpow_of_exponent_le (by linarith only [hR]) hC2
    have h2 : 1 ≤ (M : ℝ) ^ C := Real.one_le_rpow hM1 (by linarith only [hC2])
    rw [Real.rpow_two] at h1
    have h3 : 0 ≤ (2 * R) ^ C := Real.rpow_nonneg (by linarith only [hR]) _
    have h4 := mul_le_mul_of_nonneg_left h2 h3
    have h5 := mul_le_mul_of_nonneg_left hR (by linarith only [hR] : (0 : ℝ) ≤ R)
    linarith only [h1, h4, h5]

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
      rw [ext, dif_pos hkJ] at this
      exact this
    have hK : ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ ⋃ i, closedBall (x j i) (2 * R j) →
        eLpNorm (𝓕 (f : E n → ℂ)) (ENNReal.ofReal p) μ ≤
          (C * ENNReal.ofReal ((2 * R j) ^ α)) * eLpNorm f (ENNReal.ofReal p) volume :=
      fun f hf => hU (2 * R j) (by linarith only [hR1]) (M j) (x j) hsp2 f hf
    have h1 := fourier_chi_le (μ := μ) (x j) (by linarith only [hR1]) hsep (hGm k) hGsub hp
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hK
    refine h1.trans ?_
    have hchi : eLpNorm (chi (G k)) (ENNReal.ofReal p) volume ≤ volume S ^ (1 / p) := by
      unfold chi
      rw [eLpNorm_indicator_const (hGm k) (by simp; linarith only [hp]) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (by linarith only [hp])]
      simp only [enorm_one, one_mul]
      exact ENNReal.rpow_le_rpow (measure_mono Set.inter_subset_left) (by positivity)
    have hRR : ENNReal.ofReal ((2 * R j) ^ α) ≤ ENNReal.ofReal ((2 * Rmax) ^ α) :=
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by linarith only [hR1]) (by linarith only [hRle]) hα.le)
    exact mul_le_mul' (mul_le_mul' le_rfl hRR) hchi
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The choice `N ≈ log(1/α) / (2 log C₁)`. -/
lemma key_N {C₁ L : ℝ} (hC₁ : 2 ≤ C₁) (hL : 4 * Real.log (4 * C₁) < L) :
    ∃ N : ℕ, 1 ≤ N ∧ 1 / (N : ℝ) + Real.exp (-L) * C₁ ^ N ≤ (2 * Real.log C₁ + 1) / L := by
  have hlc : 0 < Real.log C₁ := Real.log_pos (by linarith only [hC₁])
  have h4 : 0 < Real.log (4 * C₁) := Real.log_pos (by linarith only [hC₁])
  have hL0 : 0 < L := by linarith only [hL, h4]
  set N := ⌈L / (2 * Real.log C₁)⌉₊
  have hpos : 0 < L / (2 * Real.log C₁) := by positivity
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hpos).ne'
  have hNge : L / (2 * Real.log C₁) ≤ N := Nat.le_ceil _
  have hNlt : (N : ℝ) < L / (2 * Real.log C₁) + 1 := Nat.ceil_lt_add_one hpos.le
  refine ⟨N, hN1, ?_⟩
  have h1 : 1 / (N : ℝ) ≤ 2 * Real.log C₁ / L := by
    rw [div_le_div_iff₀ (by positivity) hL0]
    rw [div_le_iff₀ (by positivity)] at hNge
    linarith only [hNge]
  have hpow : C₁ ^ N = Real.exp (N * Real.log C₁) := by
    rw [← Real.exp_log (show 0 < C₁ by linarith only [hC₁]), ← Real.exp_nat_mul, Real.log_exp]
  have h2 : Real.exp (-L) * C₁ ^ N ≤ 1 / L := by
    rw [hpow, ← Real.exp_add]
    have hlt : -L + N * Real.log C₁ ≤ -L / 2 + Real.log C₁ := by
      have : (N : ℝ) * Real.log C₁ ≤ (L / (2 * Real.log C₁) + 1) * Real.log C₁ :=
        mul_le_mul_of_nonneg_right hNlt.le hlc.le
      rw [add_mul, div_mul_eq_mul_div, mul_div_assoc, mul_comm 2 (Real.log C₁),
        div_mul_cancel_left₀ hlc.ne'] at this
      linarith only [this]
    refine (Real.exp_le_exp.mpr hlt).trans ?_
    rw [Real.exp_add, Real.exp_log (by linarith only [hC₁]), le_div_iff₀ hL0]
    -- `L C₁ ≤ exp(L/2)`
    have hq : 4 * C₁ < Real.exp (L / 4) := by
      rw [← Real.exp_log (show 0 < 4 * C₁ by linarith only [hC₁])]
      exact Real.exp_lt_exp.mpr (by linarith only [hL])
    have hq2 : L / 4 ≤ Real.exp (L / 4) := by linarith only [Real.add_one_le_exp (L / 4)]
    have hsq : Real.exp (L / 2) = Real.exp (L / 4) * Real.exp (L / 4) := by
      rw [← Real.exp_add]; ring_nf
    have hneg : Real.exp (-L / 2) * Real.exp (L / 2) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    have key : L * C₁ ≤ Real.exp (L / 2) := by
      rw [hsq]
      calc L * C₁ = (L / 4) * (4 * C₁) := by ring
        _ ≤ Real.exp (L / 4) * (4 * C₁) := mul_le_mul_of_nonneg_right hq2 (by linarith only [hC₁])
        _ ≤ Real.exp (L / 4) * Real.exp (L / 4) :=
          mul_le_mul_of_nonneg_left hq.le (Real.exp_pos _).le
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
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hc0 hc01 (by linarith only [hr])
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
      Real.rpow_le_rpow_of_nonpos hc0 hs (by linarith only [hr])
    calc A * N * s ^ (1 / N) * (C * (2 * A) ^ α * s ^ (1 / p))
        = (A * N * C * (2 * A) ^ α) * s ^ (1 / N) * s ^ (1 / p) := by ring
      _ ≤ (A * N * C * (2 * A) ^ α) * 1 * s ^ (1 / p) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsN hK0) (Real.rpow_nonneg hs0.le _)
      _ = (A * N * C * (2 * A) ^ α) * (s ^ r * s ^ (1 / p - r)) := by rw [hsp]; ring
      _ ≤ (A * N * C * (2 * A) ^ α) * (s ^ r * c0 ^ (1 / p - r)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsc (Real.rpow_nonneg hs0.le _)) hK0
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
  have hp0 : 0 < p := by linarith only [hp]
  have hα1 : α < 1 := lt_of_lt_of_le hαα ((min_le_left _ _).trans (by norm_num))
  set L := Real.log (1 / α)
  have hLeq : L = -Real.log α := by simp [L, Real.log_inv]
  have hLbig : 4 * Real.log (4 * C₁') < L := by
    rw [hLeq]
    have := Real.log_lt_log hα (lt_of_lt_of_le hαα (min_le_right _ _))
    rw [Real.log_exp] at this; linarith only [this]
  have hL0 : 0 < L := lt_of_le_of_lt (by
    have := Real.log_pos (show (1 : ℝ) < 4 * C₁' by linarith only [hC₁']); linarith only [this]) hLbig
  have hαexp : α = Real.exp (-L) := by rw [hLeq, neg_neg, Real.exp_log hα]
  obtain ⟨N, hN1, hNkey⟩ := key_N hC₁' hLbig
  obtain ⟨C, hC⟩ := sparse_of_thick hn hμ hC0 hA2 hL2 hp hp2 hα.le hT
  set r := 1 / p + κ / L
  have hr1 : r < 1 := by
    by_contra h
    push_neg at h
    have : 1 / q ≤ 1 := by rw [div_le_one (by linarith only [hq])]; exact hq
    linarith only [h, this, hqr]
  have hrp : 1 / p ≤ r := by
    have : 0 ≤ κ / L := div_nonneg (by
      have := Real.log_pos (show (1:ℝ) < C₁' by linarith only [hC₁']); linarith only [this]) hL0.le
    simp only [r]; linarith only [this]
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hrp
  set q₀ := 1 / r
  have hq₀ : 1 < q₀ := by rw [lt_one_div (by norm_num) hr0]; simpa using hr1
  have hq₀p : q₀ ≤ p := by
    simp only [q₀]; rw [div_le_iff₀ hr0]
    rw [div_le_iff₀ hp0] at hrp; linarith only [hrp]
  have hqq₀ : q < q₀ := by
    simp only [q₀]; rw [lt_div_iff₀ hr0]
    rw [lt_div_iff₀ (by linarith only [hq])] at hqr; linarith only [hqr]
  have hexp : 1 / (N : ℝ) + α * C₁' ^ N + 1 / p ≤ r := by
    simp only [r]; rw [hαexp]; linarith only [hNkey]
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
      linarith only [this, hab]
    calc A * max 1 s ^ C₁ ^ N ≤ A' * max 1 s ^ C₁ ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ A' * max 1 s ^ C₁' ^ N :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hu hpow)
            (zero_le_one.trans hA')
  have hmain := cube_bound_from_cover (μ := μ) hp.le hα hC (measurableSet_cubeUnion hS) hSfin
    hRb' hScov
  have hchi : chi S = S.indicator fun _ => (1 : ℂ) := rfl
  rw [← hchi]
  refine hmain.trans ?_
  have hJ' : (J : ℝ≥0∞) ≤ ENNReal.ofReal (A' * N * s ^ (1 / (N : ℝ))) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hJ.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)) (Real.rpow_nonneg hs0 _)))
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

/-! ## Dilations (copied from `restr_sparse_of_restr_uniform/Est2.lean`) -/

/-! ## `annulus_of_restr` -/

/-! ## `map_anisoLin` -/

end TaoBR.Parab.PartE

end S_PartE

namespace TaoBR.Parab
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
  haveI : ContinuousSMul ℝ (E (m + 1)) := IsBoundedSMul.continuousSMul
  haveI : T2Space (E (m + 1)) := inferInstance
  (anisoLE hlam).toContinuousLinearEquiv

@[simp] theorem anisoCLE_apply {lam : ℝ} (hlam : lam ≠ 0) (x : E (m + 1)) :
    anisoCLE hlam x = anisoLin lam x := rfl

end Coords

/-! ## The rescaled function -/

section Rescale

variable {m : ℕ}

end Rescale

/-! ## Geometry: the rescaled thickening lies in a thin annulus -/

section Geom

variable {m : ℕ}

end Geom

/-! ## Exponent bookkeeping -/

/-! ## The thickened parabolic estimate -/

end TaoBR.Parab.PartF

end S_PartF

namespace TaoBR.Parab
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
            (Real.exp_le_one_iff.2
              (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hε.le) (sq_nonneg _))) (norm_nonneg _)
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
    exact absurd this hε.ne'
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
    linarith only [hnb]
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
    linarith only [this]
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

export TaoBR.Parab.PartG (mkPoint_castSucc mkPoint_last horiz_apply continuous_mkPoint continuous_graphPt inner_graphPt hasCompactSupport_wC ph norm_ph continuous_ph ft_eq)






end Coords

variable {m : ℕ}


theorem continuous_wC (m : ℕ) : Continuous fun v : E m => ((wt m v : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (wBump m).continuous

/-! ## The Fourier transform of the paraboloid measure as an oscillatory integral (from `PartG`) -/





/-! ## Directional derivatives along a line -/

theorem fderiv_apply_of_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E m → F} {v a : E m} {d : F} (hf : DifferentiableAt ℝ f v)
    (h : HasDerivAt (fun s : ℝ => f (v + s • a)) d 0) : fderiv ℝ f v a = d := by
  haveI : ContinuousSMul ℝ (E m) := IsBoundedSMul.continuousSMul
  have h1 : HasDerivAt (fun s : ℝ => v + s • a) a 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).smul_const a).const_add v
    rwa [one_smul] at this
  have := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by rw [zero_smul, add_zero])
  exact this.unique h

theorem hasDerivAt_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E m → F} {v a : E m} (hf : DifferentiableAt ℝ f v) :
    HasDerivAt (fun s : ℝ => f (v + s • a)) (fderiv ℝ f v a) 0 := by
  haveI : ContinuousSMul ℝ (E m) := IsBoundedSMul.continuousSMul
  have h1 : HasDerivAt (fun s : ℝ => v + s • a) a 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).smul_const a).const_add v
    rwa [one_smul] at this
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by rw [zero_smul, add_zero])

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
    mul_le_mul (by linarith only [hx]) (mul_le_mul_of_nonneg_right hv (norm_nonneg _)) (by positivity)
      (by positivity)
  have h3 := neg_abs_le (vert x * ⟪v, horiz x⟫)
  linarith only [h1, h2, h3]

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
    have e1 := mul_le_mul_of_nonneg_right hD hA.le
    have e2 := mul_le_mul_of_nonneg_left hq hM
    linarith only [e1, e2, mul_nonneg hM hqpos.le]
  have h2 : |w * (-(t * A ^ 2) / q ^ 2)| ≤ 1 / A := by
    rw [abs_mul, abs_div, abs_neg, abs_mul, abs_of_nonneg hw0, abs_of_nonneg (sq_nonneg A),
      abs_of_pos (pow_pos hqpos 2)]
    have hq2 : (5 / 8 * A ^ 2) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by positivity) hq 2
    have h3 : |t| * A ^ 2 / q ^ 2 ≤ 1 / A := by
      rw [div_le_div_iff₀ (pow_pos hqpos 2) hA]
      have : |t| * A ^ 2 * A ≤ A / 4 * A ^ 2 * A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [ht]) (sq_nonneg A)) hA.le
      linarith only [this, hq2, pow_pos hA 4]
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
  haveI : ContinuousSMul ℝ (E m) := IsBoundedSMul.continuousSMul
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
  refine (pow_le_pow_iff_left₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (abs_nonneg _)) two_ne_zero).1 ?_
  linarith only [h, h1, mul_nonneg (norm_nonneg (horiz x)) (abs_nonneg (vert x))]

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
  have h1 : ‖v‖ ^ 2 ≤ 25 / 16 := by
    have := pow_le_pow_left₀ h0 hv 2
    linarith only [this]
  have h2 : ‖graphPt v‖ ^ 2 ≤ (3 / 2) ^ 2 := by
    have := mul_le_mul h1 h1 (sq_nonneg _) (by norm_num)
    linarith only [h, h1, this]
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
    linarith only [h2, sq_nonneg (‖v‖ ^ 2 / 2 - vert η)]
  linarith only [this, hv]

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
          · nlinarith only [hnx, hcase, hA1, mul_le_mul_of_nonneg_left hA1 hA]
        have := hC2 x hcase
        calc F * s ≤ F * (3 * ‖horiz x‖) := mul_le_mul_of_nonneg_left hsle hF0
          _ = 3 * (F * ‖horiz x‖) := by ring
          _ ≤ 3 * max C2 0 := by linarith only [this, hmax2]
      · right; right
        have hsle : s ≤ 3 := by
          rw [hs, Real.sqrt_le_iff]; constructor
          · norm_num
          · push Not at hA1; linarith only [hnx, hcase, hA1]
        calc F * s ≤ M * 3 := mul_le_mul hFM hsle hs0.le hM
          _ = 3 * M := by ring
    · push Not at hcase
      by_cases hB1 : 1 ≤ |vert x|
      · left
        set t := Real.sqrt |vert x| with ht
        have hsle : s ≤ 3 * t := by
          rw [hs, Real.sqrt_le_iff]; constructor
          · positivity
          · rw [mul_pow, ht, Real.sq_sqrt hB]; linarith only [hnx, hcase, hB1]
        have htle : t ≤ |vert x| ^ ((m : ℝ) / 2) := by
          rw [ht, Real.sqrt_eq_rpow]
          apply Real.rpow_le_rpow_of_exponent_le hB1
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm
          linarith only [this]
        have := hC1 x
        calc F * s ≤ F * (3 * t) := mul_le_mul_of_nonneg_left hsle hF0
          _ ≤ F * (3 * |vert x| ^ ((m : ℝ) / 2)) := by gcongr
          _ = 3 * (F * |vert x| ^ ((m : ℝ) / 2)) := by ring
          _ ≤ 3 * max C1 0 := by linarith only [this, hmax1]
      · right; right
        have hsle : s ≤ 3 := by
          rw [hs, Real.sqrt_le_iff]; constructor
          · norm_num
          · push Not at hB1; linarith only [hnx, hcase, hB1]
        calc F * s ≤ M * 3 := mul_le_mul hFM hsle hs0.le hM
          _ = 3 * M := by ring
  rcases key with h | h | h <;> linarith only [h, hmax1', hmax2', hM]

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
          hC _ (by linarith only [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) _ (tsupport_fk f k)
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
end TaoBR.Parab

section S_PBRDefs

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace

namespace TaoBR.PBR

open Parab

/-! ## Objects -/

/-- `e(t) = exp(2πit)`. -/
noncomputable def ex (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))

/-- The critical exponent `p_c = 2(m+1)/(m+2)` of Conjecture 4.4. -/
noncomputable def pc (m : ℕ) : ℝ := 2 * ((m : ℝ) + 1) / ((m : ℝ) + 2)

/-- Horizontal frequency cutoff: `1` on `closedBall 0 16`, supported in `ball 0 17`. -/
noncomputable def chiB (m : ℕ) : ContDiffBump (0 : E m) := ⟨16, 17, by norm_num, by norm_num⟩

/-- `χ(v)`. -/
noncomputable def chiH (m : ℕ) (v : E m) : ℝ := chiB m v

/-- `ϑ`: `1` on `[-1, 1]`, supported in `(-2, 2)`. -/
noncomputable def thB : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- `ζ(s) = e^{-2πs} ϑ(s)`. -/
noncomputable def zeta (s : ℝ) : ℝ := Real.exp (-(2 * Real.pi * s)) * thB s

/-- The cutoff `η(ξ) = χ(ξ̲) ζ(ξₙ - |ξ̲|²/2)` fed to the parabolic Bochner–Riesz conjecture. -/
noncomputable def etaP (m : ℕ) (ξ : E (m + 1)) : ℝ :=
  chiH m (horiz ξ) * zeta (vert ξ - ‖horiz ξ‖ ^ 2 / 2)

/-- The symbol of `parabolicBochnerRiesz (etaP m) δ` (definitionally the one in
`Def_TaoBR.parabolicBochnerRiesz`). -/
noncomputable def pSym (m : ℕ) (δ : ℝ) (ξ : E (m + 1)) : ℂ :=
  ((etaP m ξ * plusPow δ (vert ξ - ‖horiz ξ‖ ^ 2 / 2) : ℝ) : ℂ)

/-- Its kernel `K = 𝓕⁻ (η s₊^δ)`. -/
noncomputable def Kp (m : ℕ) (δ : ℝ) : E (m + 1) → ℂ := 𝓕⁻ (pSym m δ)

/-- The vertical factor `B(t) = ∫ ζ(s) s₊^δ e(ts) ds`. -/
noncomputable def Bfun (δ t : ℝ) : ℂ := ∫ s : ℝ, ((zeta s * plusPow δ s : ℝ) : ℂ) * ex (t * s)

/-- The horizontal (Fresnel) factor `E(z) = ∫ χ(v) e(⟨z̲, v⟩ + zₙ|v|²/2) dv`. -/
noncomputable def Efun (m : ℕ) (z : E (m + 1)) : ℂ :=
  ∫ v : E m, (chiH m v : ℂ) * ex (⟪horiz z, v⟫ + vert z * ‖v‖ ^ 2 / 2)

/-- The phase `φ(w) = |w̲|²/(2wₙ)`. -/
noncomputable def phiP {m : ℕ} (w : E (m + 1)) : ℝ := ‖horiz w‖ ^ 2 / (2 * vert w)

/-- `u(w) = w̲/wₙ`. -/
noncomputable def uP {m : ℕ} (w : E (m + 1)) : E m := (vert w)⁻¹ • horiz w

/-- The decay exponent `γ = δ + 1 + m/2` of the kernel. -/
noncomputable def gam (m : ℕ) (δ : ℝ) : ℝ := δ + 1 + (m : ℝ) / 2

/-- `β`: `1` on `[1, 2]`, supported in `(1/2, 5/2)`. -/
noncomputable def betaB : ContDiffBump (3 / 2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- `1` on `closedBall 0 3`, supported in `ball 0 4`. -/
noncomputable def gamB (m : ℕ) : ContDiffBump (0 : E m) := ⟨3, 4, by norm_num, by norm_num⟩

/-- `1` on `closedBall 0 1`, supported in `ball 0 2`. -/
noncomputable def thY (m : ℕ) : ContDiffBump (0 : E (m + 1)) := ⟨1, 2, by norm_num, by norm_num⟩

/-- Output cutoff `ψ(X) = β(Xₙ) γ(X̲)`: `1` where `Xₙ ∈ [1, 2]` and `|X̲| ≤ 3`; on its support
`Xₙ ∈ (1/2, 5/2)`, `|X̲| < 4`, so `|X̲/Xₙ| < 8`. -/
noncomputable def psiX (m : ℕ) (X : E (m + 1)) : ℝ := betaB (vert X) * gamB m (horiz X)

/-- Input cutoff `θ(Y)`. -/
noncomputable def thetaY (m : ℕ) (Y : E (m + 1)) : ℝ := thY m Y

/-- The rescaled cut-off PBR kernel `T_R(X, Y) = ψ(X) θ(Y) K(R²X - RY)`. -/
noncomputable def Tker (m : ℕ) (δ R : ℝ) (X Y : E (m + 1)) : ℂ :=
  ((psiX m X * thetaY m Y : ℝ) : ℂ) * Kp m δ (R ^ 2 • X - R • Y)

/-- The main term `M_R(X, Y) = ψθ wₙ^{-γ} e(-R²φ(w)) F(u(w), R⁻²/wₙ)`, `w = X - R⁻¹Y`. -/
noncomputable def Mker (m : ℕ) (δ : ℝ) (F : E m → ℝ → ℂ) (R : ℝ) (X Y : E (m + 1)) : ℂ :=
  ((psiX m X * thetaY m Y * vert (X - R⁻¹ • Y) ^ (-gam m δ) : ℝ) : ℂ) *
    ex (-(R ^ 2 * phiP (X - R⁻¹ • Y))) * F (uP (X - R⁻¹ • Y)) (R⁻¹ ^ 2 / vert (X - R⁻¹ • Y))

/-- The linearized kernel `L_R(X, Y) = ψθ Xₙ^{-γ} e(-R²φ(X) - R⟨graphPt(-u(X)), Y⟩)`. -/
noncomputable def Lker (m : ℕ) (δ R : ℝ) (X Y : E (m + 1)) : ℂ :=
  ((psiX m X * thetaY m Y * vert X ^ (-gam m δ) : ℝ) : ℂ) *
    ex (-(R ^ 2 * phiP X + R * ⟪graphPt (-uP X), Y⟫))

/-- The localized parabolic restriction estimate over `|v| ≤ 3/2`, in `ThickRestr`'s format:
`∫_{|v| ≤ 3/2} |f̂(v, |v|²/2)|^p dv ≤ C R^{αp} ‖f‖_p^p` for Schwartz `f` supported in `B(0, R)`. -/
def LocPar (m : ℕ) (p α : ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(E (m + 1), ℂ), tsupport f ⊆ closedBall 0 R →
    ∫⁻ v in closedBall (0 : E m) (3 / 2), ‖𝓕 (f : E (m + 1) → ℂ) (graphPt v)‖ₑ ^ p ≤
      C * ENNReal.ofReal (R ^ α) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p

/-! ## Small facts (proved here) -/

section Small

variable {m : ℕ}

@[simp] theorem horiz_apply (y : E (m + 1)) (i : Fin m) : horiz y i = y (Fin.castSucc i) := by
  simp [horiz]

theorem norm_sq_hv (y : E (m + 1)) : ‖y‖ ^ 2 = ‖horiz y‖ ^ 2 + vert y ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp [vert]

theorem norm_le_horiz_add_vert (y : E (m + 1)) : ‖y‖ ≤ ‖horiz y‖ + |vert y| := by
  have := norm_sq_hv y
  have h : ‖y‖ ^ 2 ≤ (‖horiz y‖ + |vert y|) ^ 2 := by
    rw [this, add_sq, sq_abs]
    linarith only [mul_nonneg (mul_nonneg zero_le_two (norm_nonneg (horiz y))) (abs_nonneg (vert y))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

theorem horiz_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : E (m + 1) => horiz ξ) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : E (m + 1) => fun i : Fin m => ξ (Fin.castSucc i)) :=
    contDiff_pi.2 fun i => (EuclideanSpace.proj (𝕜 := ℝ) (Fin.castSucc i)).contDiff
  exact (EuclideanSpace.equiv (Fin m) ℝ).symm.contDiff.comp h

theorem vert_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : E (m + 1) => vert ξ) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).contDiff

theorem zeta_contDiff : ContDiff ℝ (⊤ : ℕ∞) zeta := by
  unfold zeta
  exact (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg).mul thB.contDiff

/-- `η` is smooth. -/
theorem etaP_contDiff : ContDiff ℝ (⊤ : ℕ∞) (etaP m) := by
  unfold etaP chiH
  exact ((chiB m).contDiff.comp horiz_contDiff).mul (zeta_contDiff.comp
    (vert_contDiff.sub (((contDiff_norm_sq ℝ).comp horiz_contDiff).div_const 2)))

/-- `η` has compact support: `η(ξ) ≠ 0` forces `|ξ̲| < 17` and `|ξₙ - |ξ̲|²/2| < 2`. -/
theorem etaP_hasCompactSupport : HasCompactSupport (etaP m) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : E (m + 1)) 200)
  intro ξ hξ
  by_contra h
  have h' : chiH m (horiz ξ) * zeta (vert ξ - ‖horiz ξ‖ ^ 2 / 2) ≠ 0 := h
  have h1 : ‖horiz ξ‖ < 17 := by
    by_contra hc; push Not at hc
    exact left_ne_zero_of_mul h' ((chiB m).zero_of_le_dist (by simpa [chiB] using hc))
  have h2 : |vert ξ - ‖horiz ξ‖ ^ 2 / 2| < 2 := by
    by_contra hc; push Not at hc
    have : thB (vert ξ - ‖horiz ξ‖ ^ 2 / 2) = 0 :=
      thB.zero_of_le_dist (by simpa [thB, Real.dist_eq] using hc)
    exact right_ne_zero_of_mul h' (by simp [zeta, this])
  apply hξ
  rw [mem_closedBall, dist_zero_right]
  have h3 := norm_le_horiz_add_vert ξ
  have h4 : |vert ξ| < 2 + ‖horiz ξ‖ ^ 2 / 2 := by
    have := abs_sub_abs_le_abs_sub (vert ξ) (‖horiz ξ‖ ^ 2 / 2)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖horiz ξ‖ ^ 2 / 2)] at this
    linarith only [this, h2]
  have h5 : ‖horiz ξ‖ ^ 2 < 17 ^ 2 := pow_lt_pow_left₀ h1 (norm_nonneg _) two_ne_zero
  linarith only [h3, h4, h5, h1]

theorem pc_pos (m : ℕ) : 0 < pc m := by unfold pc; positivity

theorem one_lt_pc (m : ℕ) (hm : 1 ≤ m) : 1 < pc m := by
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold pc; rw [lt_div_iff₀ (by positivity)]; linarith

theorem pc_lt_two (m : ℕ) : pc m < 2 := by
  unfold pc; rw [div_lt_iff₀ (by positivity)]; linarith

/-- `δ(p_c) = 0`. -/
theorem critIndex_pc (m : ℕ) : critIndex (m + 1) (ENNReal.ofReal (pc m)) = 0 := by
  have hpc := pc_pos m
  rw [critIndex, ENNReal.toReal_inv, ENNReal.toReal_ofReal hpc.le]
  have h1 : (pc m)⁻¹ - 1 / 2 = 1 / (2 * ((m : ℝ) + 1)) := by unfold pc; field_simp; ring
  rw [h1, abs_of_pos (by positivity)]
  push_cast
  have h2 : ((m : ℝ) + 1) * (1 / (2 * ((m : ℝ) + 1))) - 1 / 2 = 0 := by field_simp; ring
  rw [h2, max_self]

/-- `(m+1)/p_c = (m+2)/2`. -/
theorem div_pc (m : ℕ) : ((m : ℝ) + 1) / pc m = ((m : ℝ) + 2) / 2 := by
  unfold pc; field_simp

/-- The choice of `α` in the assembly. -/
theorem exists_small_alpha (κ α₀ a b : ℝ) (hα₀ : 0 < α₀) (hab : a < b) :
    ∃ α : ℝ, 0 < α ∧ α < α₀ ∧ a + κ / Real.log (1 / α) < b := by
  set g := b - a with hg
  have hg0 : 0 < g := by linarith
  set L := max κ 0 / g + 1 with hL
  have hL0 : 0 ≤ max κ 0 / g := div_nonneg (le_max_right _ _) hg0.le
  set α := min (α₀ / 2) (Real.exp (-L)) with hα
  have hαpos : 0 < α := lt_min (by linarith) (Real.exp_pos _)
  refine ⟨α, hαpos, lt_of_le_of_lt (min_le_left _ _) (by linarith), ?_⟩
  have hlog : L ≤ Real.log (1 / α) := by
    rw [one_div, Real.log_inv, le_neg]
    calc Real.log α ≤ Real.log (Real.exp (-L)) := Real.log_le_log hαpos (min_le_right _ _)
      _ = -L := Real.log_exp _
  have hlpos : 0 < Real.log (1 / α) := by linarith
  have key : κ / Real.log (1 / α) < g := by
    rw [div_lt_iff₀ hlpos]
    have hmax : κ ≤ max κ 0 := le_max_left _ _
    have h2 : g * L ≤ g * Real.log (1 / α) := mul_le_mul_of_nonneg_left hlog hg0.le
    have h3 : g * L = max κ 0 + g := by rw [hL, mul_add, mul_div_cancel₀ _ hg0.ne', mul_one]
    linarith only [h2, h3, hmax, hg0]
  linarith

end Small

end TaoBR.PBR

end S_PBRDefs

section S_PBRPartK

/-! # Part K: `kernel_rep` -/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace

namespace TaoBR.PBR.PartK

open TaoBR.PBR TaoBR.Parab

variable {m : ℕ}

/-! ## Coordinates (copied from `proofs/parab/PartF.lean`, `proofs/thm410/PartB1.lean`) -/

@[simp] theorem mkPoint_castSucc (u : E m) (t : ℝ) (i : Fin m) :
    mkPoint u t (Fin.castSucc i) = u i := by
  simp [mkPoint]

@[simp] theorem mkPoint_last (u : E m) (t : ℝ) : mkPoint u t (Fin.last m) = t := by
  simp [mkPoint]

@[simp] theorem horiz_mkPoint (u : E m) (t : ℝ) : horiz (mkPoint u t) = u := by
  ext i; simp

@[simp] theorem vert_mkPoint (u : E m) (t : ℝ) : vert (mkPoint u t) = t := by
  simp [vert]

theorem ext_hv {y y' : E (m + 1)} (h1 : horiz y = horiz y') (h2 : vert y = vert y') : y = y' := by
  ext i
  induction i using Fin.lastCases with
  | last => exact h2
  | cast j => have := congrArg (fun z : E m => z j) h1; simpa using this

theorem mkPoint_horiz_vert (y : E (m + 1)) : mkPoint (horiz y) (vert y) = y :=
  ext_hv (by simp) (by simp)

theorem inner_mkPoint (u u' : E m) (t t' : ℝ) :
    ⟪mkPoint u t, mkPoint u' t'⟫ = ⟪u, u'⟫ + t * t' := by
  simp only [PiLp.inner_apply, Fin.sum_univ_castSucc, mkPoint_castSucc, mkPoint_last]
  simp [mul_comm]

theorem measurePreserving_mkPoint (m : ℕ) :
    MeasurePreserving (fun q : E m × ℝ => mkPoint q.1 q.2) (volume.prod volume) volume := by
  have h1 : MeasurePreserving (Prod.map (WithLp.ofLp (p := 2) (V := Fin m → ℝ)) (id : ℝ → ℝ))
      ((volume : Measure (E m)).prod (volume : Measure ℝ)) (volume.prod volume) :=
    (PiLp.volume_preserving_ofLp (Fin m)).prod (MeasurePreserving.id volume)
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure (Fin m → ℝ)))
    (ν := (volume : Measure ℝ)))
  have h3 := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm
  have h4 := PiLp.volume_preserving_toLp (Fin (m + 1))
  have h := h4.comp (h3.comp (h2.comp h1))
  have heq : (fun q : E m × ℝ => mkPoint q.1 q.2) = (WithLp.toLp 2 ∘
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm ∘
        Prod.swap ∘ Prod.map (WithLp.ofLp (p := 2) (V := Fin m → ℝ)) (id : ℝ → ℝ)) := by
    funext q
    apply ext_hv
    · ext i; simp [Function.comp]
    · simp [vert, Function.comp]
  rw [heq]; exact h

/-- The shear `(v, s) ↦ mkPoint v (s + |v|²/2)` is measure preserving. -/
theorem measurePreserving_shear (m : ℕ) :
    MeasurePreserving (fun q : E m × ℝ => mkPoint q.1 (q.2 + ‖q.1‖ ^ 2 / 2))
      (volume.prod volume) volume := by
  have hs : MeasurePreserving (fun q : E m × ℝ => (q.1, q.2 + ‖q.1‖ ^ 2 / 2))
      ((volume : Measure (E m)).prod (volume : Measure ℝ)) (volume.prod volume) := by
    refine (MeasurePreserving.id (volume : Measure (E m))).skew_product
      (g := fun (v : E m) (s : ℝ) => s + ‖v‖ ^ 2 / 2) (by fun_prop) ?_
    exact ae_of_all _ fun v => map_add_right_eq_self _ _
  exact (measurePreserving_mkPoint m).comp hs

/-! ## The symbol -/

lemma plusPow_measurable (δ : ℝ) : Measurable (fun t : ℝ => plusPow δ t) := by
  unfold plusPow
  exact Measurable.ite measurableSet_Ioi (measurable_id.pow_const δ) measurable_const

lemma plusPow_nonneg (δ t : ℝ) : 0 ≤ plusPow δ t := by
  unfold plusPow; split_ifs with h
  · exact Real.rpow_nonneg h.le _
  · exact le_rfl

/-- Integrability from a bound and a support of finite measure. -/
lemma integrable_of_bdd {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    {μ : Measure X} (f : X → F)
    (hf : AEStronglyMeasurable f μ) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) (s : Set X)
    (hs : μ s < ⊤) (hsupp : ∀ x, f x ≠ 0 → x ∈ s) : Integrable f μ := by
  have h1 : IntegrableOn f s μ :=
    Measure.integrableOn_of_bounded hs.ne hf (ae_of_all _ hb)
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h1
  intro x hx; exact hsupp x hx

lemma pSym_measurable (δ : ℝ) : Measurable (pSym m δ) := by
  unfold pSym
  have h1 : Measurable (etaP m) := etaP_contDiff.continuous.measurable
  have h2 : Measurable (fun ξ : E (m + 1) => plusPow δ (vert ξ - ‖horiz ξ‖ ^ 2 / 2)) :=
    (plusPow_measurable δ).comp (by unfold vert horiz; fun_prop)
  exact Complex.measurable_ofReal.comp (h1.mul h2)

lemma pSym_supp (δ : ℝ) (ξ : E (m + 1)) (h : pSym m δ ξ ≠ 0) : ξ ∈ tsupport (etaP m) := by
  apply subset_tsupport
  intro h0
  apply h
  simp [pSym, h0]

lemma pSym_bound (δ : ℝ) (hδ : 0 < δ) : ∃ C : ℝ, ∀ ξ, ‖pSym m δ ξ‖ ≤ C := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ ξ, ‖etaP m ξ‖ ≤ C :=
    etaP_contDiff.continuous.bounded_above_of_compact_support etaP_hasCompactSupport
  refine ⟨C * 2 ^ δ, fun ξ => ?_⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  by_cases h0 : etaP m ξ = 0
  · simp [pSym, h0]; positivity
  set s := vert ξ - ‖horiz ξ‖ ^ 2 / 2 with hs
  have hs2 : s < 2 := by
    by_contra hc; push Not at hc
    apply h0
    have : thB s = 0 := thB.zero_of_le_dist (by
      simp only [thB, Real.dist_eq, sub_zero]
      rw [abs_of_nonneg (by linarith)]; exact hc)
    simp [etaP, zeta, this, ← hs]
  have hp : plusPow δ s ≤ 2 ^ δ := by
    unfold plusPow; split_ifs with h
    · exact Real.rpow_le_rpow h.le hs2.le hδ.le
    · positivity
  rw [pSym, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (plusPow_nonneg _ _)]
  have := hC ξ
  rw [Real.norm_eq_abs] at this
  exact mul_le_mul this hp (plusPow_nonneg _ _) hC0

lemma pSym_integrable (δ : ℝ) (hδ : 0 < δ) : Integrable (pSym m δ) volume := by
  obtain ⟨C, hC⟩ := pSym_bound (m := m) δ hδ
  exact integrable_of_bdd _ (pSym_measurable δ).aestronglyMeasurable C hC _
    etaP_hasCompactSupport.isCompact.measure_lt_top (pSym_supp δ)

/-! ## Items 1–3 -/

theorem parab_eq_kernel (δ : ℝ) (hδ : 0 < δ) (g : 𝓢(E (m + 1), ℂ)) (x : E (m + 1)) :
    parabolicBochnerRiesz (etaP m) δ (g : E (m + 1) → ℂ) x = ∫ y, Kp m δ (x - y) * g y := by
  have hm := pSym_integrable (m := m) δ hδ
  have hmm : Measurable (pSym m δ) := pSym_measurable δ
  have hg : Integrable (g : E (m + 1) → ℂ) volume := g.integrable
  change multiplier (pSym m δ) (g : E (m + 1) → ℂ) x = _
  simp only [multiplier, Kp, Real.fourierInv_eq', Real.fourier_eq', smul_eq_mul]
  set F : E (m + 1) → E (m + 1) → ℂ := fun ξ y =>
    Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I) * pSym m δ ξ *
      (Complex.exp (↑(-2 * Real.pi * ⟪y, ξ⟫) * Complex.I) * g y) with hF
  have hint : Integrable (Function.uncurry F) ((volume : Measure (E (m + 1))).prod volume) := by
    refine Integrable.mono' (hm.norm.mul_prod hg.norm) ?_ ?_
    · apply Measurable.aestronglyMeasurable
      simp only [hF, Function.uncurry_def]
      have : Measurable (fun p : E (m + 1) × E (m + 1) => (g p.2 : ℂ)) :=
        g.continuous.measurable.comp measurable_snd
      have h2 : Measurable (fun p : E (m + 1) × E (m + 1) => pSym m δ p.1) :=
        hmm.comp measurable_fst
      exact (((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_fst.inner continuous_const))).mul
          continuous_const)).measurable).mul h2).mul
        ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
          (continuous_const.mul (continuous_snd.inner continuous_fst))).mul
            continuous_const)).measurable.mul this)
    · refine ae_of_all _ fun p => ?_
      simp only [hF, Function.uncurry_def, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact le_rfl
  have h1 : ∀ ξ, Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I) *
      (pSym m δ ξ * ∫ y, Complex.exp (↑(-2 * Real.pi * ⟪y, ξ⟫) * Complex.I) * g y) =
      ∫ y, F ξ y := by
    intro ξ
    simp only [hF]
    rw [← integral_const_mul, ← integral_const_mul]; congr 1; funext y; ring
  simp_rw [h1]
  rw [integral_integral_swap hint]
  congr 1; funext y
  rw [← integral_mul_const]
  congr 1; funext ξ
  simp only [hF]
  have : Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I) *
      Complex.exp (↑(-2 * Real.pi * ⟪y, ξ⟫) * Complex.I) =
      Complex.exp (↑(2 * Real.pi * ⟪ξ, x - y⟫) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1
    rw [inner_sub_right, real_inner_comm y ξ]; push_cast; ring
  rw [← this]; ring

lemma Kp_eq_fourierIntegral (δ : ℝ) :
    Kp m δ = VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ (E (m + 1)))
      (pSym m δ) := rfl

theorem Kp_continuous (δ : ℝ) (hδ : 0 < δ) : Continuous (Kp m δ) := by
  rw [Kp_eq_fourierIntegral]
  refine VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar ?_
    (pSym_integrable δ hδ)
  simp only [LinearMap.neg_apply, innerₗ_apply_apply]
  fun_prop

theorem Kp_bounded (δ : ℝ) : ∃ M : ℝ, ∀ z, ‖Kp m δ z‖ ≤ M := by
  refine ⟨∫ ξ : E (m + 1), ‖pSym m δ ξ‖, fun z => ?_⟩
  rw [Kp, Real.fourierInv_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext ξ; rw [Circle.norm_smul]

/-! ## Item 4: the factorization -/

lemma fourierChar_eq_ex (x : ℝ) : ((𝐞 x : Circle) : ℂ) = ex x := by
  rw [Real.fourierChar_apply, ex]; congr 1; push_cast; ring

lemma ex_add (a b : ℝ) : ex (a + b) = ex a * ex b := by
  rw [ex, ex, ex, ← Complex.exp_add]; congr 1; push_cast; ring

lemma integrand_shear (δ : ℝ) (z : E (m + 1)) (v : E m) (s : ℝ) :
    𝐞 ⟪mkPoint v (s + ‖v‖ ^ 2 / 2), z⟫ • pSym m δ (mkPoint v (s + ‖v‖ ^ 2 / 2)) =
      ((chiH m v : ℂ) * ex (⟪horiz z, v⟫ + vert z * ‖v‖ ^ 2 / 2)) *
        (((zeta s * plusPow δ s : ℝ) : ℂ) * ex (vert z * s)) := by
  have hz : ⟪mkPoint v (s + ‖v‖ ^ 2 / 2), z⟫ =
      (⟪horiz z, v⟫ + vert z * ‖v‖ ^ 2 / 2) + vert z * s := by
    conv_lhs => rw [← mkPoint_horiz_vert z]
    rw [inner_mkPoint, real_inner_comm]; ring
  have hs : s + ‖v‖ ^ 2 / 2 - ‖v‖ ^ 2 / 2 = s := by ring
  rw [Circle.smul_def, hz, fourierChar_eq_ex, ex_add, smul_eq_mul]
  simp only [pSym, etaP, horiz_mkPoint, vert_mkPoint, hs]
  push_cast; ring

theorem Kp_factor (δ : ℝ) (z : E (m + 1)) : Kp m δ z = Bfun δ (vert z) * Efun m z := by
  have hΦ := measurePreserving_shear m
  have hgm : Measurable (fun ξ : E (m + 1) => 𝐞 ⟪ξ, z⟫ • pSym m δ ξ) := by
    have h1 : Measurable (fun ξ : E (m + 1) => ((𝐞 ⟪ξ, z⟫ : Circle) : ℂ)) :=
      (Real.continuous_fourierChar.subtype_val.comp (by fun_prop)).measurable
    simp_rw [Circle.smul_def]
    exact h1.mul (pSym_measurable δ)
  rw [Kp, Real.fourierInv_eq, ← hΦ.map_eq,
    integral_map hΦ.measurable.aemeasurable (hgm.aestronglyMeasurable)]
  simp_rw [integrand_shear]
  rw [integral_prod_mul (μ := (volume : Measure (E m))) (ν := (volume : Measure ℝ))
    (fun v : E m => (chiH m v : ℂ) * ex (⟪horiz z, v⟫ + vert z * ‖v‖ ^ 2 / 2))
    (fun s : ℝ => ((zeta s * plusPow δ s : ℝ) : ℂ) * ex (vert z * s)), Bfun, Efun, mul_comm]

/-- **K (kernel representation and factorization).** -/
theorem kernel_rep (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (∀ (f : 𝓢(E (m + 1), ℂ)) (x : E (m + 1)),
      parabolicBochnerRiesz (etaP m) δ (f : E (m + 1) → ℂ) x = ∫ y, Kp m δ (x - y) * f y) ∧
    Continuous (Kp m δ) ∧ (∃ M : ℝ, ∀ z, ‖Kp m δ z‖ ≤ M) ∧
    ∀ z : E (m + 1), Kp m δ z = Bfun δ (vert z) * Efun m z :=
  ⟨fun f x => parab_eq_kernel δ hδ f x, Kp_continuous δ hδ, Kp_bounded δ,
    fun z => Kp_factor δ z⟩

end TaoBR.PBR.PartK

end S_PBRPartK

namespace TaoBR.PBR
alias kernel_rep := TaoBR.PBR.PartK.kernel_rep
end TaoBR.PBR

section S_PBRPartB

/-! # Part B: `Bfun_asymp` -/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace

namespace TaoBR.PBR.PartB

open TaoBR.PBR Filter Topology

/-! ### The real pieces `w = s₊^δ e^{-2πs}` and `h = (1 - ϑ) w` -/

/-- `w(s) = s₊^δ e^{-2πs}`. -/
noncomputable def wF (δ s : ℝ) : ℝ := plusPow δ s * Real.exp (-(2 * Real.pi * s))

/-- `h(s) = (1 - ϑ(s)) w(s)`. -/
noncomputable def hF (δ s : ℝ) : ℝ := (1 - thB s) * wF δ s

/-- The smooth model of `h` on `s > 0`. -/
noncomputable def hU (δ s : ℝ) : ℝ := (1 - thB s) * (s ^ δ * Real.exp (-(2 * Real.pi) * s))

theorem thB_eq_one {s : ℝ} (hs : |s| ≤ 1) : thB s = 1 :=
  ContDiffBump.one_of_mem_closedBall _ (by rw [mem_closedBall, Real.dist_eq, sub_zero]; exact hs)

theorem hF_eq_zero (δ : ℝ) {s : ℝ} (hs : s < 1) : hF δ s = 0 := by
  unfold hF wF plusPow
  by_cases h0 : 0 < s
  · rw [thB_eq_one (by rw [abs_le]; constructor <;> linarith)]; ring
  · simp [h0]

theorem hF_eventuallyEq_zero (δ : ℝ) {s : ℝ} (hs : s < 1) : hF δ =ᶠ[𝓝 s] fun _ => 0 :=
  Filter.eventually_of_mem (Iio_mem_nhds hs) fun _ hy => hF_eq_zero δ hy

theorem hF_eventuallyEq_hU (δ : ℝ) {s : ℝ} (hs : 0 < s) : hF δ =ᶠ[𝓝 s] hU δ :=
  Filter.eventually_of_mem (Ioi_mem_nhds hs) fun y hy => by
    simp only [hF, wF, hU, plusPow, if_pos (show (0 : ℝ) < y from hy), neg_mul]

theorem hU_contDiffAt (δ : ℝ) {s : ℝ} (hs : 0 < s) : ContDiffAt ℝ (⊤ : ℕ∞) (hU δ) s := by
  unfold hU
  exact (contDiffAt_const.sub thB.contDiff.contDiffAt).mul
    ((Real.contDiffAt_rpow_const_of_ne hs.ne').mul
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffAt)

theorem hF_contDiff (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (hF δ) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s < 1
  · exact contDiffAt_const.congr_of_eventuallyEq (hF_eventuallyEq_zero δ hs)
  · push Not at hs
    exact (hU_contDiffAt δ (by linarith)).congr_of_eventuallyEq (hF_eventuallyEq_hU δ (by linarith))

/-! ### Derivative bounds for `h` -/

theorem iteratedDeriv_rpow (δ : ℝ) (i : ℕ) {s : ℝ} (hs : 0 < s) :
    iteratedDeriv i (fun x : ℝ => x ^ δ) s = (∏ j ∈ Finset.range i, (δ - j)) * s ^ (δ - i) := by
  induction i generalizing s with
  | zero => simp
  | succ i ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv i (fun x : ℝ => x ^ δ) =ᶠ[𝓝 s]
        fun x => (∏ j ∈ Finset.range i, (δ - j)) * x ^ (δ - i) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hs) fun y hy => ih hy
    rw [heq.deriv_eq, ((Real.hasDerivAt_rpow_const (p := δ - i) (Or.inl hs.ne')).const_mul _).deriv,
      Finset.prod_range_succ]
    push_cast
    rw [show δ - ((i : ℝ) + 1) = δ - i - 1 by ring]
    ring

theorem one_sub_thB_bound (i : ℕ) :
    ∃ M : ℝ, ∀ s, ‖iteratedDeriv i (fun s => 1 - thB s) s‖ ≤ M := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine ⟨1, fun s => ?_⟩
    simp only [iteratedDeriv_zero, Real.norm_eq_abs]
    rw [abs_le]; constructor <;> linarith [thB.nonneg (x := s), thB.le_one (x := s)]
  · obtain ⟨M, hM⟩ := (thB.contDiff.continuous_iteratedFDeriv (m := i) (n := (⊤ : ℕ∞))
      (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (thB.hasCompactSupport.iteratedFDeriv i)
    refine ⟨M, fun s => ?_⟩
    rw [iteratedDeriv_const_sub hi, iteratedDeriv_neg, norm_neg,
      ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hM s

theorem leib {f g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (n : ℕ) (hf : ContDiffOn ℝ n f U)
    (hg : ContDiffOn ℝ n g U) {s : ℝ} (hs : s ∈ U) {A B : ℕ → ℝ} {X₁ X₂ : ℝ}
    (hA : ∀ i, ‖iteratedDeriv i f s‖ ≤ A i * X₁) (hB : ∀ i, ‖iteratedDeriv i g s‖ ≤ B i * X₂) :
    ‖iteratedDeriv n (fun y => f y * g y) s‖ ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i * B (n - i)) * (X₁ * X₂) := by
  have key := norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hs (n := n) le_rfl
  have e : ∀ (F : ℝ → ℝ) (k : ℕ), ‖iteratedFDerivWithin ℝ k F U s‖ = ‖iteratedDeriv k F s‖ :=
    fun F k => by
      rw [iteratedFDerivWithin_of_isOpen k hU hs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp only [e] at key
  refine key.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have hA0 : 0 ≤ A i * X₁ := (norm_nonneg _).trans (hA i)
  have hB0 : 0 ≤ B (n - i) * X₂ := (norm_nonneg _).trans (hB _)
  calc (n.choose i : ℝ) * ‖iteratedDeriv i f s‖ * ‖iteratedDeriv (n - i) g s‖
      ≤ (n.choose i : ℝ) * (A i * X₁) * (B (n - i) * X₂) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hA i) (Nat.cast_nonneg _)) (hB _) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) hA0)
    _ = _ := by ring

theorem wU_bound (δ : ℝ) (m : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    ‖iteratedDeriv m (fun x : ℝ => x ^ δ * Real.exp (-(2 * Real.pi) * x)) s‖ ≤
      (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * |∏ j ∈ Finset.range i, (δ - j)| *
        (2 * Real.pi) ^ (m - i)) * (s ^ δ * Real.exp (-(2 * Real.pi) * s)) := by
  have hs0 : 0 < s := by linarith
  refine leib (f := fun x : ℝ => x ^ δ) (g := fun x : ℝ => Real.exp (-(2 * Real.pi) * x))
    isOpen_Ioi m (fun x hx => (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt)
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffOn (mem_Ioi.2 hs0)
    (fun i => ?_) (fun i => ?_)
  · rw [iteratedDeriv_rpow δ i hs0, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
    gcongr
    linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
  · rw [iteratedDeriv_exp_const_mul, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_neg, abs_of_pos (by positivity), abs_of_pos (Real.exp_pos _)]

theorem rpow_mul_exp_le (δ : ℝ) {s : ℝ} (hs : 1 ≤ s) :
    s ^ δ * Real.exp (-(2 * Real.pi) * s) ≤
      ((⌈δ⌉₊).factorial / Real.pi ^ ⌈δ⌉₊) * Real.exp (-(Real.pi * s)) := by
  set N := ⌈δ⌉₊
  have hs0 : 0 < s := by linarith
  have h1 : s ^ δ ≤ s ^ N := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hs (Nat.le_ceil δ)
  have h2 : (Real.pi * s) ^ N / N.factorial ≤ Real.exp (Real.pi * s) :=
    Real.pow_div_factorial_le_exp _ (by positivity) N
  have h3 : s ^ N ≤ N.factorial / Real.pi ^ N * Real.exp (Real.pi * s) := by
    rw [mul_pow, div_le_iff₀ (by positivity)] at h2
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  calc s ^ δ * Real.exp (-(2 * Real.pi) * s)
      ≤ (N.factorial / Real.pi ^ N * Real.exp (Real.pi * s)) * Real.exp (-(2 * Real.pi) * s) :=
        mul_le_mul_of_nonneg_right (h1.trans h3) (Real.exp_pos _).le
    _ = _ := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem hF_deriv_bound (δ : ℝ) (n : ℕ) :
    ∃ K : ℝ, ∀ s, ‖iteratedDeriv n (hF δ) s‖ ≤
      (Ici (1 : ℝ)).indicator (fun s => K * Real.exp (-(Real.pi * s))) s := by
  choose M hM using one_sub_thB_bound
  set Kw : ℕ → ℝ := fun m => ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
    |∏ j ∈ Finset.range i, (δ - j)| * (2 * Real.pi) ^ (m - i)
  set K1 := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * M i * Kw (n - i)
  set N := ⌈δ⌉₊
  refine ⟨K1 * (N.factorial / Real.pi ^ N), fun s => ?_⟩
  by_cases hs : 1 ≤ s
  · rw [indicator_of_mem (mem_Ici.2 hs)]
    have hs0 : 0 < s := by linarith
    rw [((hF_eventuallyEq_hU δ hs0).iteratedDeriv n).eq_of_nhds]
    have hb := leib (f := fun s => 1 - thB s)
      (g := fun x : ℝ => x ^ δ * Real.exp (-(2 * Real.pi) * x)) isOpen_Ioi n
      (contDiffOn_const.sub thB.contDiff.contDiffOn)
      (fun x hx => ((Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).mul
        (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffAt).contDiffWithinAt)
      (mem_Ioi.2 hs0) (A := M) (X₁ := 1) (B := Kw)
      (X₂ := s ^ δ * Real.exp (-(2 * Real.pi) * s))
      (fun i => by rw [mul_one]; exact hM i s) (fun i => wU_bound δ i hs)
    have hK1 : 0 ≤ K1 := by
      have := (norm_nonneg _).trans hb
      rw [one_mul] at this
      exact nonneg_of_mul_nonneg_left this (by positivity)
    calc ‖iteratedDeriv n (hU δ) s‖ ≤ K1 * (1 * (s ^ δ * Real.exp (-(2 * Real.pi) * s))) := hb
      _ ≤ K1 * ((N.factorial / Real.pi ^ N) * Real.exp (-(Real.pi * s))) := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_left (rpow_mul_exp_le δ hs) hK1
      _ = _ := by ring
  · push Not at hs
    rw [indicator_of_notMem (by simpa using hs), ((hF_eventuallyEq_zero δ hs).iteratedDeriv n).eq_of_nhds]
    simp

theorem hF_deriv_integrable (δ : ℝ) (n : ℕ) : Integrable (iteratedDeriv n (hF δ)) := by
  obtain ⟨K, hK⟩ := hF_deriv_bound δ n
  refine Integrable.mono' ?_ ((hF_contDiff δ).continuous_iteratedDeriv n
    (by exact_mod_cast le_top)).aestronglyMeasurable (ae_of_all _ hK)
  refine (integrable_indicator_iff measurableSet_Ici).2 ?_
  refine IntegrableOn.mono_set ?_ (Ici_subset_Ioi.2 zero_lt_one)
  have := (exp_neg_integrableOn_Ioi 0 Real.pi_pos).const_mul K
  simp only [neg_mul] at this
  exact this

/-! ### The remainder `r(t) = ∫ h(s) e(ts) ds` decays faster than any power -/

/-- `h` as a complex function. -/
noncomputable def hC (δ s : ℝ) : ℂ := ((hF δ s : ℝ) : ℂ)

theorem hC_contDiff (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (hC δ) :=
  Complex.ofRealCLM.contDiff.comp (hF_contDiff δ)

theorem iteratedDeriv_hC (δ : ℝ) (n : ℕ) :
    iteratedDeriv n (hC δ) = fun s => ((iteratedDeriv n (hF δ) s : ℝ) : ℂ) := by
  induction n with
  | zero => funext s; simp [hC]
  | succ n ih =>
    funext s
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    exact ((((hF_contDiff δ).differentiable_iteratedDeriv n
      (by exact_mod_cast ENat.natCast_lt_top n)) s).hasDerivAt.ofReal_comp).deriv

theorem fourier_hC_bound (δ : ℝ) (n : ℕ) :
    ∃ L : ℝ, ∀ x : ℝ, ‖𝓕 (hC δ) x‖ * |x| ^ n ≤ L := by
  refine ⟨∫ s, ‖iteratedDeriv n (hF δ) s‖, fun x => ?_⟩
  have hI : ∀ k : ℕ, (k : ℕ∞) ≤ (⊤ : ℕ∞) → Integrable (iteratedDeriv k (hC δ)) := fun k _ => by
    rw [iteratedDeriv_hC]; exact (hF_deriv_integrable δ k).ofReal
  have key := congrFun (Real.fourier_iteratedDeriv (hC_contDiff δ) hI (le_top : (n : ℕ∞) ≤ ⊤)) x
  have hle : ‖𝓕 (iteratedDeriv n (hC δ)) x‖ ≤ ∫ s, ‖iteratedDeriv n (hF δ) s‖ := by
    rw [Real.fourier_real_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext s
    rw [Circle.norm_smul, iteratedDeriv_hC, Complex.norm_real]
  rw [key, norm_smul, norm_pow] at hle
  have h2 : ‖(2 * Real.pi * Complex.I * x : ℂ)‖ = 2 * Real.pi * |x| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [h2] at hle
  have h3 : |x| ^ n ≤ (2 * Real.pi * |x|) ^ n :=
    pow_le_pow_left₀ (abs_nonneg x)
      (le_mul_of_one_le_left (abs_nonneg x) (by linarith only [Real.pi_gt_three])) n
  calc ‖𝓕 (hC δ) x‖ * |x| ^ n ≤ ‖𝓕 (hC δ) x‖ * (2 * Real.pi * |x|) ^ n :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = (2 * Real.pi * |x|) ^ n * ‖𝓕 (hC δ) x‖ := mul_comm _ _
    _ ≤ _ := hle

theorem r_eq (δ t : ℝ) : ∫ s : ℝ, (hF δ s : ℂ) * ex (t * s) = 𝓕 (hC δ) (-t) := by
  rw [Real.fourier_real_eq]
  congr 1; funext s
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, ex, hC, mul_comm]
  congr 1; congr 1
  push_cast; ring

theorem r_decay (δ k : ℝ) : ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
    ‖∫ s : ℝ, (hF δ s : ℂ) * ex (t * s)‖ ≤ C * t ^ (-k) := by
  obtain ⟨L, hL⟩ := fourier_hC_bound δ ⌈k⌉₊
  refine ⟨L, fun t ht => ?_⟩
  rw [r_eq]
  have h := hL (-t)
  rw [abs_neg, abs_of_pos (by linarith)] at h
  have htn : 0 < t ^ ⌈k⌉₊ := by positivity
  have h1 : ‖𝓕 (hC δ) (-t)‖ ≤ L * (t ^ ⌈k⌉₊)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ htn]; exact h
  refine h1.trans ?_
  have hL0 : 0 ≤ L := (mul_nonneg (norm_nonneg _) htn.le).trans h
  refine mul_le_mul_of_nonneg_left ?_ hL0
  rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le ht (by linarith [Nat.le_ceil k])

/-! ### The Gamma integral with a complex rate -/

/-- `L(r) = ∫_0^∞ s^δ e^{-rs} ds`. -/
noncomputable def Lint (δ : ℝ) (r : ℂ) : ℂ :=
  ∫ s in Ioi (0 : ℝ), ((s ^ δ : ℝ) : ℂ) * Complex.exp (-(r * s))

theorem norm_Lint_integrand (δ : ℝ) (r : ℂ) {s : ℝ} (hs : 0 < s) :
    ‖((s ^ δ : ℝ) : ℂ) * Complex.exp (-(r * s))‖ = s ^ δ * Real.exp (-r.re * s) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hs.le _),
    Complex.norm_exp]
  congr 2; simp [neg_mul]

theorem integ_rpow_exp {β c : ℝ} (hβ : -1 < β) (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => s ^ β * Real.exp (-c * s)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hβ one_pos hc
  simpa [Real.rpow_one] using this

theorem Lint_integrand_continuous (δ : ℝ) (hδ : 0 < δ) (r : ℂ) :
    Continuous (fun s : ℝ => ((s ^ δ : ℝ) : ℂ) * Complex.exp (-(r * s))) :=
  (Complex.continuous_ofReal.comp (Real.continuous_rpow_const hδ.le)).mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg)

theorem Lint_integrable (δ : ℝ) (hδ : 0 < δ) {r : ℂ} (hr : 0 < r.re) :
    IntegrableOn (fun s : ℝ => ((s ^ δ : ℝ) : ℂ) * Complex.exp (-(r * s))) (Ioi 0) := by
  refine Integrable.mono' (integ_rpow_exp (β := δ) (by linarith) hr)
    (Lint_integrand_continuous δ hδ r).aestronglyMeasurable ?_
  exact (ae_restrict_iff' measurableSet_Ioi).2
    (ae_of_all _ fun s hs => (norm_Lint_integrand δ r hs).le)

theorem Lint_ofReal (δ : ℝ) (hδ : 0 < δ) {r : ℝ} (hr : 0 < r) :
    Lint δ r = (1 / (r : ℂ)) ^ ((δ + 1 : ℝ) : ℂ) * Complex.Gamma ((δ + 1 : ℝ) : ℂ) := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := ((δ + 1 : ℝ) : ℂ))
    (by simp; linarith) hr
  rw [← h, Lint]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  rw [Complex.ofReal_cpow (le_of_lt hs)]
  congr 2; push_cast; ring

theorem Lint_differentiableOn (δ : ℝ) (hδ : 0 < δ) :
    DifferentiableOn ℂ (Lint δ) {r : ℂ | 0 < r.re} := by
  intro r0 hr0
  have hr0' : 0 < r0.re := hr0
  set c := r0.re / 2 with hc_def
  have hc : 0 < c := by positivity
  have hball : ∀ r ∈ ball r0 c, c < r.re := fun r hr => by
    rw [mem_ball, dist_eq_norm] at hr
    have h1 := Complex.abs_re_le_norm (r - r0)
    rw [Complex.sub_re] at h1
    have h2 := (abs_lt.1 (h1.trans_lt hr)).1
    linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (r : ℂ) (s : ℝ) => ((s ^ δ : ℝ) : ℂ) * Complex.exp (-(r * s)))
    (F' := fun (r : ℂ) (s : ℝ) => ((s ^ δ : ℝ) : ℂ) * (Complex.exp (-(r * s)) * -(1 * (s : ℂ))))
    (bound := fun s => s ^ (δ + 1) * Real.exp (-c * s)) (x₀ := r0)
    (ball_mem_nhds r0 hc)
    (Eventually.of_forall fun r => (Lint_integrand_continuous δ hδ r).aestronglyMeasurable)
    (Lint_integrable δ hδ hr0')
    (by
      refine Continuous.aestronglyMeasurable ?_
      exact (Complex.continuous_ofReal.comp (Real.continuous_rpow_const hδ.le)).mul
        ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg).mul
          (continuous_const.mul Complex.continuous_ofReal).neg))
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs r hr => by
      have hs' : (0 : ℝ) < s := hs
      rw [show ((s ^ δ : ℝ) : ℂ) * (Complex.exp (-(r * s)) * -(1 * (s : ℂ))) =
          -(((s ^ δ : ℝ) : ℂ) * Complex.exp (-(r * s)) * (s : ℂ)) by ring,
        norm_neg, norm_mul, norm_Lint_integrand δ r hs', Complex.norm_real,
        Real.norm_of_nonneg hs'.le, Real.rpow_add_one hs'.ne', mul_right_comm]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
      have := hball r hr
      nlinarith only [this, hs']))
    (integ_rpow_exp (by linarith) hc)
    (ae_of_all _ fun s r _ =>
      (((hasDerivAt_id' r).mul_const (s : ℂ)).neg.cexp.const_mul _))
  exact key.2.differentiableAt.differentiableWithinAt

theorem Lint_eq (δ : ℝ) (hδ : 0 < δ) {r : ℂ} (hr : 0 < r.re) :
    Lint δ r = (1 / r) ^ ((δ + 1 : ℝ) : ℂ) * Complex.Gamma ((δ + 1 : ℝ) : ℂ) := by
  set U : Set ℂ := {r : ℂ | 0 < r.re} with hU_def
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (Lint δ) U := (Lint_differentiableOn δ hδ).analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (fun r : ℂ => (1 / r) ^ ((δ + 1 : ℝ) : ℂ) *
      Complex.Gamma ((δ + 1 : ℝ) : ℂ)) U := by
    refine DifferentiableOn.analyticOnNhd (fun r hr => ?_) hU
    have hr' : 0 < r.re := hr
    have hr0 : r ≠ 0 := fun h => by simp [h] at hr'
    refine (DifferentiableAt.mul_const ?_ _).differentiableWithinAt
    refine ((differentiableAt_const _).div differentiableAt_id hr0).cpow_const ?_
    show (1 : ℂ) / r ∈ Complex.slitPlane
    rw [Complex.mem_slitPlane_iff]; left
    rw [one_div, Complex.inv_re]; exact div_pos hr' (Complex.normSq_pos.2 hr0)
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h1 : (1 : ℂ) ∈ U := by simp [U]
  have ht : Tendsto (fun n : ℕ => (((1 + 1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1))) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at this
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 1).comp this
    · rw [mem_compl_singleton_iff]
      intro h
      have h' := Complex.ofReal_injective (h.trans Complex.ofReal_one.symm)
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), Lint δ z = (1 / z) ^ ((δ + 1 : ℝ) : ℂ) *
      Complex.Gamma ((δ + 1 : ℝ) : ℂ) :=
    ht.frequently (Eventually.of_forall fun n => Lint_ofReal δ hδ (by positivity)).frequently
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hpre h1 hfreq hr

/-! ### Assembly -/

theorem norm_ex (x : ℝ) : ‖ex x‖ = 1 := by
  rw [ex, Complex.norm_exp]; simp

theorem Bfun_split (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    Bfun δ t = Lint δ (2 * Real.pi * (1 - Complex.I * t)) -
      ∫ s : ℝ, (hF δ s : ℂ) * ex (t * s) := by
  have hre : 0 < (2 * Real.pi * (1 - Complex.I * t) : ℂ).re := by simp [Real.pi_pos]
  have hw : (fun s : ℝ => ((wF δ s : ℝ) : ℂ) * ex (t * s)) = (Ioi (0 : ℝ)).indicator
      (fun s : ℝ => ((s ^ δ : ℝ) : ℂ) *
        Complex.exp (-((2 * Real.pi * (1 - Complex.I * t) : ℂ) * s))) := by
    funext s
    by_cases hs : 0 < s
    · rw [indicator_of_mem (mem_Ioi.2 hs), wF, plusPow, if_pos hs, Complex.ofReal_mul, mul_assoc,
        Complex.ofReal_exp, ex, ← Complex.exp_add]
      congr 2; push_cast; ring
    · rw [indicator_of_notMem (by simpa using hs), wF, plusPow, if_neg hs]; simp
  have hwi : Integrable (fun s : ℝ => ((wF δ s : ℝ) : ℂ) * ex (t * s)) := by
    rw [hw]; exact (integrable_indicator_iff measurableSet_Ioi).2 (Lint_integrable δ hδ hre)
  have hhi : Integrable (fun s : ℝ => ((hF δ s : ℝ) : ℂ) * ex (t * s)) := by
    refine Integrable.mono' (hF_deriv_integrable δ 0).norm ?_ (ae_of_all _ fun s => ?_)
    · exact ((Complex.continuous_ofReal.comp (hF_contDiff δ).continuous).mul
        (by unfold ex; fun_prop)).aestronglyMeasurable
    · rw [norm_mul, norm_ex, mul_one, Complex.norm_real, iteratedDeriv_zero]
  have hsplit : (fun s : ℝ => ((zeta s * plusPow δ s : ℝ) : ℂ) * ex (t * s)) =
      fun s => ((wF δ s : ℝ) : ℂ) * ex (t * s) - ((hF δ s : ℝ) : ℂ) * ex (t * s) := by
    funext s; simp only [zeta, wF, hF]; push_cast; ring
  rw [Bfun, hsplit, integral_sub hwi hhi, hw, integral_indicator measurableSet_Ioi]
  rfl

theorem ofReal_mul_cpow' {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : z ≠ 0) (a : ℂ) :
    ((x : ℂ) * z) ^ a = (x : ℂ) ^ a * z ^ a := by
  have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hx' hz), Complex.cpow_def_of_ne_zero hx',
    Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul hx hz, ← Complex.ofReal_log hx.le,
    add_mul, Complex.exp_add]

theorem sub_I_ne_zero (σ : ℝ) : (σ : ℂ) - Complex.I ≠ 0 := fun h => by
  have := congrArg Complex.im h; simp at this

theorem g_contDiff (a K : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun σ : ℝ => (1 / ((σ : ℂ) - Complex.I)) ^ a / K) := by
  rw [contDiff_iff_contDiffAt]
  intro σ
  have hne := sub_I_ne_zero σ
  have hslit : 1 / ((σ : ℂ) - Complex.I) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right
    rw [one_div, Complex.inv_im]
    have : Complex.normSq ((σ : ℂ) - Complex.I) ≠ 0 := (Complex.normSq_pos.2 hne).ne'
    simp [this]
  have h1 : ContDiffAt ℂ (⊤ : ℕ∞) (fun z : ℂ => (1 / (z - Complex.I)) ^ a) (σ : ℂ) := by
    have e : (fun z : ℂ => (1 / (z - Complex.I)) ^ a) =ᶠ[𝓝 (σ : ℂ)]
        fun z => Complex.exp (Complex.log (1 / (z - Complex.I)) * a) := by
      filter_upwards [(continuous_id.sub continuous_const).continuousAt.eventually_ne hne]
        with z hz
      rw [Complex.cpow_def_of_ne_zero (one_div_ne_zero (show z - Complex.I ≠ 0 from hz))]
    refine ContDiffAt.congr_of_eventuallyEq ?_ e
    refine Complex.contDiff_exp.contDiffAt.comp _ (ContDiffAt.mul ?_ contDiffAt_const)
    refine ContDiffAt.comp (g := Complex.log) (f := fun z : ℂ => 1 / (z - Complex.I)) (σ : ℂ)
      (Complex.contDiffAt_log hslit) ?_
    exact contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) hne
  have h2 := (h1.restrict_scalars ℝ).comp σ Complex.ofRealCLM.contDiff.contDiffAt
  exact h2.div_const K

/-- **B (vertical asymptotics).** Verbatim from the Blueprint. -/
theorem Bfun_asymp (δ : ℝ) (hδ : 0 < δ) :
    ∃ cB : ℂ, cB ≠ 0 ∧ ∃ g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧ g 0 = 1 ∧
      ∀ k : ℝ, ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
        ‖Bfun δ t - cB * ((t ^ (-(δ + 1)) : ℝ) : ℂ) * g t⁻¹‖ ≤ C * t ^ (-k) := by
  set a : ℂ := ((δ + 1 : ℝ) : ℂ) with ha_def
  have ha : 0 < a.re := by simp [a]; linarith
  set K : ℂ := (1 / (((0 : ℝ) : ℂ) - Complex.I)) ^ a with hK_def
  have hK : K ≠ 0 := by
    rw [hK_def, Ne, Complex.cpow_eq_zero_iff, not_and_or]
    left; exact one_div_ne_zero (sub_I_ne_zero 0)
  refine ⟨Complex.Gamma a * ((((2 * Real.pi)⁻¹) ^ (δ + 1) : ℝ) : ℂ) * K, ?_,
    fun σ => (1 / ((σ : ℂ) - Complex.I)) ^ a / K, g_contDiff a K, div_self hK, fun k => ?_⟩
  · refine mul_ne_zero (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos ha) ?_) hK
    exact Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (by positivity) _).ne'
  obtain ⟨C, hC⟩ := r_decay δ k
  refine ⟨C, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hre : 0 < (2 * Real.pi * (1 - Complex.I * t) : ℂ).re := by simp [Real.pi_pos]
  rw [Bfun_split δ hδ t, Lint_eq δ hδ hre]
  have hfac : (1 / (2 * Real.pi * (1 - Complex.I * t)) : ℂ) =
      (((2 * Real.pi)⁻¹ * t⁻¹ : ℝ) : ℂ) * (1 / (((t⁻¹ : ℝ) : ℂ) - Complex.I)) := by
    have h1 := sub_I_ne_zero t⁻¹
    have h2 : (1 - Complex.I * t : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this
    have h3 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0.ne'
    have h4 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_pos.ne'
    have h5 : ((t : ℂ)⁻¹ - Complex.I) * t = 1 - Complex.I * t := by
      field_simp
    push_cast
    rw [← h5]
    field_simp
  have hpow : ((((2 * Real.pi)⁻¹ * t⁻¹ : ℝ) : ℂ)) ^ a =
      ((((2 * Real.pi)⁻¹) ^ (δ + 1) : ℝ) : ℂ) * ((t ^ (-(δ + 1)) : ℝ) : ℂ) := by
    rw [ha_def, ← Complex.ofReal_cpow (by positivity), Real.mul_rpow (by positivity) (by positivity),
      Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le]
    push_cast; ring
  rw [hfac, ofReal_mul_cpow' (by positivity) (one_div_ne_zero (sub_I_ne_zero _)), hpow]
  set W := (1 / (((t⁻¹ : ℝ) : ℂ) - Complex.I)) ^ a
  set A := ((((2 * Real.pi)⁻¹) ^ (δ + 1) : ℝ) : ℂ)
  set T := ((t ^ (-(δ + 1)) : ℝ) : ℂ)
  set R := ∫ s : ℝ, (hF δ s : ℂ) * ex (t * s)
  have e : Complex.Gamma a * A * K * T * (W / K) = A * T * W * Complex.Gamma a := by
    field_simp
  rw [e, sub_sub_cancel_left, norm_neg]
  exact hC t ht

end TaoBR.PBR.PartB

end S_PBRPartB

namespace TaoBR.PBR
alias Bfun_asymp := TaoBR.PBR.PartB.Bfun_asymp
end TaoBR.PBR

section S_PBRPartE

/-! # Part E: `Efun_eq` -/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace

namespace TaoBR.PBR.PartE

open TaoBR.PBR Filter Complex
open scoped Topology Real

variable {m : ℕ}

/-! ## `χ` as a Schwartz map and Fourier inversion (adapted from `proofs/parab/PartG.lean`) -/

theorem hasCompactSupport_chiC (m : ℕ) : HasCompactSupport fun v : E m => ((chiH m v : ℝ) : ℂ) :=
  (chiB m).hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero

theorem contDiff_chiC (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) fun v : E m => ((chiH m v : ℝ) : ℂ) :=
  Complex.ofRealCLM.contDiff.comp (chiB m).contDiff

/-- `χ` as a Schwartz map. -/
noncomputable def W (m : ℕ) : 𝓢(E m, ℂ) :=
  (hasCompactSupport_chiC m).toSchwartzMap (contDiff_chiC m)

/-- `χ̂`. -/
noncomputable def Wh (m : ℕ) : 𝓢(E m, ℂ) := 𝓕 (W m)

theorem W_apply (v : E m) : W m v = ((chiH m v : ℝ) : ℂ) := rfl

theorem inv_formula (v : E m) :
    ((chiH m v : ℝ) : ℂ) = ∫ ξ, cexp (((2 * π * ⟪ξ, v⟫ : ℝ) : ℂ) * I) * Wh m ξ := by
  have h := (W m).continuous.fourierInv_fourier_eq (W m).integrable (Wh m).integrable
  have h2 := congrFun h v
  rw [Real.fourierInv_eq'] at h2
  rw [← W_apply, ← h2]
  rfl

/-! ## The damped integral -/

theorem ex_eq (s : ℝ) : ex s = cexp (((2 * π * s : ℝ) : ℂ) * I) := by
  unfold ex; congr 1; push_cast; ring

theorem norm_ex (s : ℝ) : ‖ex s‖ = 1 := by
  rw [ex_eq]; exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_ex : Continuous ex := by
  unfold ex; fun_prop

/-- The damped integral `I_ε`. -/
noncomputable def Ieps (z : E (m + 1)) (ε : ℝ) : ℂ :=
  ∫ v, cexp (-(ε : ℂ) * ‖v‖ ^ 2) *
    (((chiH m v : ℝ) : ℂ) * ex (⟪horiz z, v⟫ + vert z * ‖v‖ ^ 2 / 2))

theorem tendsto_Ieps (z : E (m + 1)) :
    Tendsto (Ieps z) (𝓝[>] 0) (𝓝 (Efun m z)) := by
  have hw : Continuous fun v : E m => ((chiH m v : ℝ) : ℂ) := (W m).continuous
  have hph : Continuous fun v : E m => ex (⟪horiz z, v⟫ + vert z * ‖v‖ ^ 2 / 2) :=
    continuous_ex.comp ((continuous_const.inner continuous_id).add
      ((continuous_const.mul (continuous_norm.pow 2)).div_const 2))
  unfold Ieps Efun
  apply tendsto_integral_filter_of_dominated_convergence (fun v => ‖W m v‖)
  · exact Eventually.of_forall fun ε =>
      ((Complex.continuous_exp.comp (continuous_const.mul
        ((Complex.continuous_ofReal.comp continuous_norm).pow 2))).mul
          (hw.mul hph)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine ae_of_all _ fun v => ?_
    have he : (-(ε : ℂ) * ‖v‖ ^ 2) = ((-ε * ‖v‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, norm_mul, norm_ex, mul_one, W_apply, he, Complex.norm_exp_ofReal]
    calc Real.exp (-ε * ‖v‖ ^ 2) * ‖((chiH m v : ℝ) : ℂ)‖ ≤ 1 * ‖((chiH m v : ℝ) : ℂ)‖ :=
          mul_le_mul_of_nonneg_right
            (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖v‖])) (norm_nonneg _)
      _ = _ := one_mul _
  · exact (W m).integrable.norm
  · refine ae_of_all _ fun v => ?_
    have hc : Continuous fun ε : ℝ =>
        cexp (-(ε : ℂ) * ‖v‖ ^ 2) *
          (((chiH m v : ℝ) : ℂ) * ex (⟪horiz z, v⟫ + vert z * ‖v‖ ^ 2 / 2)) :=
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.neg.mul continuous_const)).mul
        continuous_const
    have := hc.tendsto 0
    simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul] at this
    exact this.mono_left nhdsWithin_le_nhds

/-- `b = ε - π i zₙ`. -/
noncomputable def bb (z : E (m + 1)) (ε : ℝ) : ℂ := (ε : ℂ) - ((π * vert z : ℝ) : ℂ) * I

/-- The Gaussian factor `(π/b)^{m/2} exp((2πi)²|ξ + z̲|²/(4b))`. -/
noncomputable def Gk (z : E (m + 1)) (ε : ℝ) (ξ : E m) : ℂ :=
  (π / bb z ε) ^ (Module.finrank ℝ (E m) / 2 : ℂ) *
    cexp ((2 * π * I) ^ 2 * ‖ξ + horiz z‖ ^ 2 / (4 * bb z ε))

theorem Ieps_eq (z : E (m + 1)) {ε : ℝ} (hε : 0 < ε) :
    Ieps z ε = ∫ ξ, Wh m ξ * Gk z ε ξ := by
  have hb : 0 < (bb z ε).re := by simp [bb, hε]
  have key : ∀ v ξ : E m, cexp (-(ε : ℂ) * ‖v‖ ^ 2) *
      (cexp (((2 * π * ⟪ξ, v⟫ : ℝ) : ℂ) * I) * Wh m ξ *
        ex (⟪horiz z, v⟫ + vert z * ‖v‖ ^ 2 / 2)) =
      Wh m ξ * cexp (-bb z ε * ‖v‖ ^ 2 + (2 * π * I) * ⟪ξ + horiz z, v⟫) := by
    intro v ξ
    rw [ex_eq, inner_add_left]
    unfold bb
    calc _ = Wh m ξ * (cexp (-(ε : ℂ) * ‖v‖ ^ 2) * cexp (((2 * π * ⟪ξ, v⟫ : ℝ) : ℂ) * I) *
          cexp (((2 * π * (⟪horiz z, v⟫ + vert z * ‖v‖ ^ 2 / 2) : ℝ) : ℂ) * I)) := by ring
      _ = _ := by
          rw [← Complex.exp_add, ← Complex.exp_add]
          congr 2
          push_cast
          ring
  have h1 : ∀ v : E m, cexp (-(ε : ℂ) * ‖v‖ ^ 2) *
      (((chiH m v : ℝ) : ℂ) * ex (⟪horiz z, v⟫ + vert z * ‖v‖ ^ 2 / 2)) =
      ∫ ξ, Wh m ξ * cexp (-bb z ε * ‖v‖ ^ 2 + (2 * π * I) * ⟪ξ + horiz z, v⟫) := by
    intro v
    rw [inv_formula v, ← integral_mul_const, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun ξ => key v ξ)
  have hint : Integrable (Function.uncurry fun (v : E m) (ξ : E m) =>
      Wh m ξ * cexp (-bb z ε * ‖v‖ ^ 2 + (2 * π * I) * ⟪ξ + horiz z, v⟫))
      (volume.prod volume) := by
    have hg : Integrable (fun v : E m => cexp (-(ε : ℂ) * ‖v‖ ^ 2 + 0 * ⟪(0 : E m), v⟫)) :=
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa using hε) 0 0
    refine (hg.norm.mul_prod (Wh m).integrable.norm).mono' ?_ (ae_of_all _ fun q => ?_)
    · apply Continuous.aestronglyMeasurable
      have := (Wh m).continuous
      fun_prop
    · obtain ⟨v, ξ⟩ := q
      simp only [Function.uncurry_apply_pair, norm_mul]
      rw [mul_comm]
      apply le_of_eq
      congr 1
      rw [Complex.norm_exp, Complex.norm_exp]
      congr 1
      have e1 : ((‖v‖ : ℂ) ^ 2) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [e1]
      simp [bb, Complex.mul_re]
      right
      rw [← Complex.ofReal_pow, Complex.ofReal_im]
  unfold Ieps
  rw [integral_congr_ae (ae_of_all _ h1), integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb]
  rfl

theorem bb_im (z : E (m + 1)) (ε : ℝ) : (bb z ε).im = -(π * vert z) := by
  simp [bb]

theorem bb_re (z : E (m + 1)) (ε : ℝ) : (bb z ε).re = ε := by
  simp [bb]

theorem bb_ne_zero (z : E (m + 1)) (ε : ℝ) (ht : 0 < vert z) : bb z ε ≠ 0 := fun h => by
  have := congrArg Complex.im h
  rw [bb_im, Complex.zero_im] at this
  have : 0 < π * vert z := mul_pos Real.pi_pos ht
  linarith

theorem hfin (m : ℕ) : (Module.finrank ℝ (E m) / 2 : ℂ) = (((m : ℝ) / 2 : ℝ) : ℂ) := by
  rw [finrank_euclideanSpace_fin]; push_cast; ring

theorem gauss_bound (z : E (m + 1)) {ε : ℝ} (hε : 0 ≤ ε) (ht : 0 < vert z) (w : E m) :
    ‖Gk z ε w‖ ≤ (vert z)⁻¹ ^ ((m : ℝ) / 2) := by
  have hb0 := bb_ne_zero z ε ht
  unfold Gk
  rw [norm_mul, hfin, Complex.norm_cpow_real]
  have hnb : π * vert z ≤ ‖bb z ε‖ := by
    have := Complex.abs_im_le_norm (bb z ε)
    rw [bb_im, abs_neg, abs_of_pos (mul_pos Real.pi_pos ht)] at this
    exact this
  have hbpos : 0 < ‖bb z ε‖ := norm_pos_iff.2 hb0
  have h1 : ‖(π : ℂ) / bb z ε‖ ≤ (vert z)⁻¹ := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, div_le_iff₀ hbpos,
      inv_mul_eq_div, le_div_iff₀ ht]
    linarith
  have h2 : ‖cexp ((2 * π * I) ^ 2 * ‖w + horiz z‖ ^ 2 / (4 * bb z ε))‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    have hI : (2 * (π : ℂ) * I) ^ 2 = -4 * π ^ 2 := by rw [mul_pow, I_sq]; ring
    have : (2 * π * I) ^ 2 * (‖w + horiz z‖ : ℂ) ^ 2 / (4 * bb z ε) =
        ((-(π ^ 2 * ‖w + horiz z‖ ^ 2) : ℝ) : ℂ) * (bb z ε)⁻¹ := by
      rw [hI]; push_cast; field_simp
    rw [this, Complex.re_ofReal_mul, Complex.inv_re, bb_re]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity))
      (div_nonneg hε (Complex.normSq_nonneg _))
  calc ‖(π : ℂ) / bb z ε‖ ^ ((m : ℝ) / 2) *
        ‖cexp ((2 * π * I) ^ 2 * ‖w + horiz z‖ ^ 2 / (4 * bb z ε))‖
      ≤ (vert z)⁻¹ ^ ((m : ℝ) / 2) * 1 :=
        mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) h1 (by positivity)) h2 (norm_nonneg _)
          (by positivity)
    _ = _ := mul_one _

theorem pi_div_bb0 (z : E (m + 1)) (ht : 0 < vert z) :
    (π : ℂ) / bb z 0 = (((vert z)⁻¹ : ℝ) : ℂ) * I := by
  have hb0 := bb_ne_zero z 0 ht
  have ht' : (vert z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  rw [div_eq_iff hb0]
  simp only [bb]
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem tendsto_rhs (z : E (m + 1)) (ht : 0 < vert z) :
    Tendsto (fun ε => ∫ ξ, Wh m ξ * Gk z ε ξ) (𝓝[>] 0) (𝓝 (∫ ξ, Wh m ξ * Gk z 0 ξ)) := by
  have hbc : Continuous (bb z) := by unfold bb; fun_prop
  have hW := (Wh m).continuous
  apply tendsto_integral_filter_of_dominated_convergence
    (fun ξ => ‖Wh m ξ‖ * (vert z)⁻¹ ^ ((m : ℝ) / 2))
  · exact Eventually.of_forall fun ε => by
      apply Continuous.aestronglyMeasurable
      unfold Gk
      exact hW.mul (continuous_const.mul (Complex.continuous_exp.comp
        ((continuous_const.mul ((Complex.continuous_ofReal.comp
          (continuous_norm.comp (continuous_id.add continuous_const))).pow 2)).div_const _)))
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine ae_of_all _ fun ξ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (gauss_bound z hε.le ht ξ) (norm_nonneg _)
  · exact (Wh m).integrable.norm.mul_const _
  · refine ae_of_all _ fun ξ => ?_
    have hb0 := bb_ne_zero z 0 ht
    have h1 : ContinuousAt (fun ε => (π : ℂ) / bb z ε) 0 :=
      continuousAt_const.div hbc.continuousAt hb0
    have hslit : (π : ℂ) / bb z 0 ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      right
      rw [pi_div_bb0 z ht]
      simp [(inv_pos.2 ht).ne']
    have h2 : ContinuousAt (fun ε => ((π : ℂ) / bb z ε) ^ (Module.finrank ℝ (E m) / 2 : ℂ)) 0 :=
      (continuousAt_cpow_const hslit).comp (f := fun ε => (π : ℂ) / bb z ε) h1
    have h3 : ContinuousAt
        (fun ε => cexp ((2 * π * I) ^ 2 * ‖ξ + horiz z‖ ^ 2 / (4 * bb z ε))) 0 :=
      Complex.continuous_exp.continuousAt.comp
        (continuousAt_const.div (continuousAt_const.mul hbc.continuousAt)
          (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hb0))
    exact ((continuousAt_const.mul (h2.mul h3)).tendsto).mono_left nhdsWithin_le_nhds

theorem Efun_eq_int (z : E (m + 1)) (ht : 0 < vert z) :
    Efun m z = ∫ ξ, Wh m ξ * Gk z 0 ξ := by
  refine tendsto_nhds_unique (tendsto_Ieps z) ((tendsto_rhs z ht).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (Ieps_eq z hε).symm

/-! ## The amplitude `A` as a Fourier integral -/

/-- The pairing `⟨(ξ, s), (a, σ)⟩ = ⟪ξ, a⟫ + s σ` on `E m × ℝ`. -/
noncomputable def Lp1 (m : ℕ) : (E m × ℝ) →L[ℝ] (E m × ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ : E m →L[ℝ] E m →L[ℝ] ℝ).bilinearComp (ContinuousLinearMap.fst ℝ (E m) ℝ)
      (ContinuousLinearMap.fst ℝ (E m) ℝ)

noncomputable def Lp2 (m : ℕ) : (E m × ℝ) →L[ℝ] (E m × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.snd ℝ (E m) ℝ)
      (ContinuousLinearMap.snd ℝ (E m) ℝ)

noncomputable def Lp (m : ℕ) : (E m × ℝ) →L[ℝ] (E m × ℝ) →L[ℝ] ℝ := Lp1 m + Lp2 m

theorem Lp_apply (p q : E m × ℝ) : Lp m p q = ⟪p.1, q.1⟫ + p.2 * q.2 := by
  rfl

/-- `ξ ↦ (ξ, |ξ|²/2)`. -/
noncomputable def lift (m : ℕ) (ξ : E m) : E m × ℝ := (ξ, ‖ξ‖ ^ 2 / 2)

theorem continuous_lift : Continuous (lift m) := by unfold lift; fun_prop

/-- The push-forward of Lebesgue measure to the paraboloid in `E m × ℝ`. -/
noncomputable def muP (m : ℕ) : Measure (E m × ℝ) := volume.map (lift m)

/-- The density `χ̂(ξ)`. -/
noncomputable def fP (m : ℕ) (p : E m × ℝ) : ℂ := Wh m p.1

/-- `A(a, σ) = ∫ χ̂(ξ) e(-(⟪ξ, a⟫ + σ|ξ|²/2)) dξ`. -/
noncomputable def Afun (m : ℕ) (a : E m) (σ : ℝ) : ℂ :=
  VectorFourier.fourierIntegral 𝐞 (muP m) (Lp m).toLinearMap₁₂ (fP m) (a, σ)

theorem Afun_eq (a : E m) (σ : ℝ) :
    Afun m a σ = ∫ ξ, cexp (((2 * π * -(⟪ξ, a⟫ + ‖ξ‖ ^ 2 / 2 * σ) : ℝ) : ℂ) * I) * Wh m ξ := by
  have hW := (Wh m).continuous
  have hfun : (fun p : E m × ℝ => 𝐞 (-(Lp m).toLinearMap₁₂ p (a, σ)) • fP m p) =
      fun p => cexp (((2 * π * -(⟪p.1, a⟫ + p.2 * σ) : ℝ) : ℂ) * I) * Wh m p.1 := by
    funext p
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul,
      ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, Lp_apply]
    rfl
  have hc : Continuous fun p : E m × ℝ =>
      cexp (((2 * π * -(⟪p.1, a⟫ + p.2 * σ) : ℝ) : ℂ) * I) * Wh m p.1 :=
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_const.mul
      ((continuous_fst.inner continuous_const).add (continuous_snd.mul continuous_const)).neg)).mul
        continuous_const)).mul (hW.comp continuous_fst)
  unfold Afun VectorFourier.fourierIntegral muP
  rw [hfun, integral_map continuous_lift.aemeasurable hc.aestronglyMeasurable]
  rfl

theorem mom (n : ℕ) : Integrable (fun p : E m × ℝ => ‖p‖ ^ n * ‖fP m p‖) (muP m) := by
  have hW := (Wh m).continuous
  unfold muP
  rw [integrable_map_measure (Continuous.aestronglyMeasurable (by unfold fP; fun_prop))
    continuous_lift.aemeasurable]
  refine ((Wh m).integrable.norm.add ((Wh m).integrable_pow_mul volume (2 * n))).mono'
    (Continuous.aestronglyMeasurable (by unfold fP lift; fun_prop)) (ae_of_all _ fun ξ => ?_)
  simp only [Function.comp, lift, fP, norm_mul, norm_pow, norm_norm, Pi.add_apply]
  have hb : ‖((ξ, ‖ξ‖ ^ 2 / 2) : E m × ℝ)‖ ^ n ≤ 1 + ‖ξ‖ ^ (2 * n) := by
    by_cases h : ‖ξ‖ ≤ 1
    · have : ‖((ξ, ‖ξ‖ ^ 2 / 2) : E m × ℝ)‖ ≤ 1 := by
        rw [norm_prod_le_iff]
        refine ⟨h, ?_⟩
        rw [Real.norm_of_nonneg (by positivity)]
        have := pow_le_one₀ (norm_nonneg ξ) h (n := 2)
        linarith only [this]
      have h1 := pow_le_one₀ (norm_nonneg _) this (n := n)
      have h2 : 0 ≤ ‖ξ‖ ^ (2 * n) := pow_nonneg (norm_nonneg _) _
      linarith only [h1, h2]
    · push Not at h
      have : ‖((ξ, ‖ξ‖ ^ 2 / 2) : E m × ℝ)‖ ≤ ‖ξ‖ ^ 2 := by
        rw [norm_prod_le_iff]
        refine ⟨le_self_pow₀ h.le two_ne_zero, ?_⟩
        rw [Real.norm_of_nonneg (by positivity)]
        exact half_le_self (sq_nonneg _)
      have := pow_le_pow_left₀ (norm_nonneg _) this n
      rw [← pow_mul] at this
      linarith only [this]
  have := mul_le_mul_of_nonneg_right hb (norm_nonneg (Wh m ξ))
  rw [add_mul, one_mul] at this
  exact this

theorem Afun_contDiff : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (Afun m)) :=
  VectorFourier.contDiff_fourierIntegral (μ := muP m) (Lp m) (f := fP m) (N := ⊤)
    (fun n _ => mom n)

theorem Afun_zero (a : E m) (ha : ‖a‖ ≤ 16) : Afun m a 0 = 1 := by
  have h1 : chiH m (-a) = 1 := by
    apply (chiB m).one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right, norm_neg]
    exact ha
  rw [Afun_eq]
  have h2 := inv_formula (m := m) (-a)
  rw [h1, Complex.ofReal_one] at h2
  rw [h2]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp [inner_neg_right]

/-! ## The constant -/

/-- `c_E = i^{m/2}`. -/
noncomputable def cE (m : ℕ) : ℂ := I ^ ((((m : ℝ) / 2 : ℝ)) : ℂ)

theorem cE_ne_zero : cE m ≠ 0 := by
  unfold cE
  rw [Ne, cpow_eq_zero_iff]
  exact fun h => I_ne_zero h.1

theorem Gk_zero (z : E (m + 1)) (ht : 0 < vert z) (ξ : E m) :
    Gk z 0 ξ = cE m * ((vert z ^ (-((m : ℝ) / 2)) : ℝ) : ℂ) * ex (-phiP z) *
      cexp (((2 * π * -(⟪ξ, uP z⟫ + ‖ξ‖ ^ 2 / 2 * (vert z)⁻¹) : ℝ) : ℂ) * I) := by
  have ht0 : (0 : ℝ) < (vert z)⁻¹ := inv_pos.2 ht
  have hcp : ∀ (r : ℝ) (y : ℂ), 0 < r → (((r : ℝ) : ℂ) * I) ^ y = ((r : ℝ) : ℂ) ^ y * I ^ y := by
    intro r y hr
    rw [cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.2 hr.ne') I_ne_zero),
      log_ofReal_mul hr I_ne_zero, cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hr.ne'),
      cpow_def_of_ne_zero I_ne_zero, ← Complex.ofReal_log hr.le, add_mul, Complex.exp_add]
  have hpow : ((π : ℂ) / bb z 0) ^ (Module.finrank ℝ (E m) / 2 : ℂ) =
      cE m * ((vert z ^ (-((m : ℝ) / 2)) : ℝ) : ℂ) := by
    rw [pi_div_bb0 z ht, hfin, hcp _ _ ht0, ← Complex.ofReal_cpow ht0.le, Real.rpow_neg ht.le,
      Real.inv_rpow ht.le, cE, mul_comm]
  have hexp : cexp ((2 * π * I) ^ 2 * ‖ξ + horiz z‖ ^ 2 / (4 * bb z 0)) =
      ex (-phiP z) * cexp (((2 * π * -(⟪ξ, uP z⟫ + ‖ξ‖ ^ 2 / 2 * (vert z)⁻¹) : ℝ) : ℂ) * I) := by
    rw [ex_eq, ← Complex.exp_add]
    congr 1
    have hb0 := bb_ne_zero z 0 ht
    have ht' : (vert z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    rw [div_eq_iff (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hb0)]
    unfold phiP uP
    rw [real_inner_smul_right, ← Complex.ofReal_pow, norm_add_sq_real]
    simp only [bb]
    push_cast
    field_simp
    ring_nf
  unfold Gk
  rw [hpow, hexp]
  ring

theorem Efun_eq (m : ℕ) (hm : 1 ≤ m) :
    ∃ cE : ℂ, cE ≠ 0 ∧ ∃ A : E m → ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry A) ∧
      (∀ a : E m, ‖a‖ ≤ 16 → A a 0 = 1) ∧
      ∀ z : E (m + 1), 0 < vert z →
        Efun m z = cE * ((vert z ^ (-((m : ℝ) / 2)) : ℝ) : ℂ) * ex (-phiP z) * A (uP z) (vert z)⁻¹ := by
  refine ⟨cE m, cE_ne_zero, Afun m, Afun_contDiff, Afun_zero, fun z ht => ?_⟩
  rw [Efun_eq_int z ht, Afun_eq, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only
  rw [Gk_zero z ht]
  ring

end TaoBR.PBR.PartE

end S_PBRPartE

namespace TaoBR.PBR
alias Efun_eq := TaoBR.PBR.PartE.Efun_eq
end TaoBR.PBR

section S_PBRPartT

/-! # Part T: `opNorm_T_le` -/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace

namespace TaoBR.PBR.PartT

open TaoBR.PBR TaoBR.Parab

/-! ## Kernel operators (copied from `proofs/restr_two_mul_of_br/Blueprint.lean`) -/

section Ops

variable {n : ℕ}

lemma eLpNorm_comp_smul (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (g : E n → ℂ) (R : ℝ)
    (hR : 0 < R) :
    eLpNorm (fun y => g (R • y)) p volume =
      ENNReal.ofReal (R ^ (-((n : ℝ) / p.toReal))) * eLpNorm g p volume := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have hmap := Measure.map_addHaar_smul (volume : Measure (E n)) hR.ne'
  have h1 : ∫⁻ x, ‖g (R • x)‖ₑ ^ p.toReal =
      ENNReal.ofReal (|(R ^ Module.finrank ℝ (E n))⁻¹|) * ∫⁻ x, ‖g x‖ₑ ^ p.toReal := by
    rw [← smul_eq_mul, ← lintegral_smul_measure, ← hmap]
    haveI : MeasurableConstSMul ℝ (E n) := ⟨fun c => (continuous_const_smul c).measurable⟩
    exact (lintegral_map_equiv (fun x => ‖g x‖ₑ ^ p.toReal) (MeasurableEquiv.smul₀ R hR.ne')).symm
  rw [h1, finrank_euclideanSpace_fin, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  congr 2
  rw [abs_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_neg hR.le,
    ← Real.rpow_mul hR.le]
  congr 1; field_simp

lemma kernelOp_aesm (k : E n → E n → ℂ) (hk : Continuous (Function.uncurry k)) (u : E n → ℂ)
    (hu : AEStronglyMeasurable u volume) : AEStronglyMeasurable (kernelOp k u) volume := by
  have h : AEStronglyMeasurable (fun z : E n × E n => k z.1 z.2 * u z.2)
      ((volume : Measure (E n)).prod volume) :=
    hk.aestronglyMeasurable.mul hu.comp_snd
  exact h.integral_prod_right'

lemma kernelOp_integrable (p : ℝ≥0∞) (hp : 1 ≤ p) (k : E n → E n → ℂ)
    (hk : Continuous (Function.uncurry k)) (M A : ℝ) (hM : ∀ x y, ‖k x y‖ ≤ M)
    (hA : ∀ x y, k x y ≠ 0 → ‖x‖ ≤ A ∧ ‖y‖ ≤ A) (u : E n → ℂ) (hu : MemLp u p volume)
    (x : E n) : Integrable (fun y => k x y * u y) volume := by
  haveI : IsFiniteMeasure (volume.restrict (closedBall (0 : E n) A)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have hu1 : Integrable u (volume.restrict (closedBall (0 : E n) A)) :=
    (hu.restrict _).integrable hp
  have hk1 : Continuous (k x) := hk.comp (Continuous.prodMk_right x)
  have h2 : IntegrableOn (fun y => k x y * u y) (closedBall (0 : E n) A) volume :=
    hu1.bdd_mul hk1.aestronglyMeasurable.restrict (ae_of_all _ (hM x))
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h2
  intro y hy
  have : k x y ≠ 0 := left_ne_zero_of_mul hy
  simpa using (hA x y this).2

lemma kernelOp_bound (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤) (k : E n → E n → ℂ)
    (hk : Continuous (Function.uncurry k)) (M A : ℝ) (hM : ∀ x y, ‖k x y‖ ≤ M)
    (hA : ∀ x y, k x y ≠ 0 → ‖x‖ ≤ A ∧ ‖y‖ ≤ A) (u : E n → ℂ) (hu : MemLp u p volume) :
    eLpNorm (kernelOp k u) p volume ≤
      (ENNReal.ofReal M * volume (closedBall (0 : E n) A) ^ (1 - 1 / p.toReal) *
        volume (closedBall (0 : E n) A) ^ (1 / p.toReal)) * eLpNorm u p volume := by
  set B := closedBall (0 : E n) A
  have hp1 : 1 ≤ p.toReal := by
    have := (ENNReal.toReal_le_toReal (by simp) hpt).2 hp; simpa using this
  set c : ℝ≥0∞ := ENNReal.ofReal M * (eLpNorm u p volume * volume B ^ (1 - 1 / p.toReal))
  have hct : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
    hu.eLpNorm_ne_top (ENNReal.rpow_ne_top_of_nonneg (by
      have : 1 / p.toReal ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
      linarith) measure_closedBall_lt_top.ne))
  have hpt' : ∀ x, ‖kernelOp k u x‖ₑ ≤ ‖B.indicator (fun _ => c.toReal) x‖ₑ := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hct]
      calc ‖kernelOp k u x‖ₑ ≤ ∫⁻ y, ‖k x y * u y‖ₑ := enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ y, B.indicator (fun y => ENNReal.ofReal M * ‖u y‖ₑ) y := by
          apply lintegral_mono; intro y
          by_cases hy : y ∈ B
          · rw [Set.indicator_of_mem hy]
            show ‖k x y * u y‖ₑ ≤ _
            rw [enorm_mul]
            gcongr
            rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hM x y)
          · rw [Set.indicator_of_notMem hy]
            have : k x y = 0 := by
              by_contra h; exact hy (by simpa [B] using (hA x y h).2)
            simp [this]
        _ = ENNReal.ofReal M * ∫⁻ y in B, ‖u y‖ₑ := by
          rw [lintegral_indicator measurableSet_closedBall, lintegral_const_mul' _ _
            ENNReal.ofReal_ne_top]
        _ ≤ c := by
          simp only [c]
          gcongr
          have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict B)
            (p := 1) (q := p) hp hu.aestronglyMeasurable.restrict
          rw [eLpNorm_one_eq_lintegral_enorm, Measure.restrict_apply_univ] at h1
          refine h1.trans ?_
          simp only [ENNReal.toReal_one, div_one]
          gcongr
          exact Measure.restrict_le_self
    · have : kernelOp k u x = 0 := by
        simp only [kernelOp]
        apply integral_eq_zero_of_ae; apply ae_of_all; intro y
        have : k x y = 0 := by
          by_contra h; exact hx (by simpa [B] using (hA x y h).1)
        simp [this]
      simp [this]
  refine (eLpNorm_mono_enorm hpt').trans ((eLpNorm_indicator_const_le _ p).trans ?_)
  rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hct]
  simp only [c]
  apply le_of_eq; ring

/-- Density: a bound on Schwartz functions for a bounded compactly supported kernel extends
to the operator norm. -/
lemma opNorm_le_of_schwartz (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤) (k : E n → E n → ℂ)
    (hk : Continuous (Function.uncurry k)) (M A : ℝ) (hM : ∀ x y, ‖k x y‖ ≤ M)
    (hA : ∀ x y, k x y ≠ 0 → ‖x‖ ≤ A ∧ ‖y‖ ≤ A) (D : ℝ≥0∞) (hDt : D ≠ ⊤)
    (hD : ∀ g : 𝓢(E n, ℂ), eLpNorm (kernelOp k g) p volume ≤ D * eLpNorm g p volume) :
    opNorm p p (kernelOp k) ≤ D := by
  apply sInf_le
  intro f hf
  set L : ℝ≥0∞ := ENNReal.ofReal M * volume (closedBall (0 : E n) A) ^ (1 - 1 / p.toReal) *
        volume (closedBall (0 : E n) A) ^ (1 / p.toReal) with hL
  have hp1 : 1 ≤ p.toReal := by
    have := (ENNReal.toReal_le_toReal (by simp) hpt).2 hp; simpa using this
  have hLt : L ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg ?_ measure_closedBall_lt_top.ne))
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_closedBall_lt_top.ne)
    have : 1 / p.toReal ≤ 1 := by rw [div_le_one (by linarith only [hp1])]; exact hp1
    linarith only [this]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set δ : ℝ := ε / (D.toReal + L.toReal + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨g, hg1, hg2, hg3⟩ := hf.exist_eLpNorm_sub_le hpt hp hδ0
  set gs : 𝓢(E n, ℂ) := hg1.toSchwartzMap hg2
  have hgs : (gs : E n → ℂ) = g := rfl
  have hgm : MemLp g p volume := hgs ▸ gs.memLp p volume
  have hfg : MemLp (f - g) p volume := hf.sub hgm
  have hsplit : kernelOp k f = kernelOp k g + kernelOp k (f - g) := by
    funext x
    simp only [kernelOp, Pi.add_apply, Pi.sub_apply, mul_sub]
    rw [← integral_add (kernelOp_integrable p hp k hk M A hM hA g hgm x)]
    · congr 1; funext y; ring
    · exact (kernelOp_integrable p hp k hk M A hM hA f hf x).sub
        (kernelOp_integrable p hp k hk M A hM hA g hgm x)
  have h1 : eLpNorm (kernelOp k f) p volume ≤ D * eLpNorm g p volume + L * ENNReal.ofReal δ := by
    rw [hsplit]
    refine (eLpNorm_add_le (kernelOp_aesm k hk g hgm.1) (kernelOp_aesm k hk _ hfg.1) hp).trans ?_
    exact add_le_add (hD gs)
      ((kernelOp_bound p hp hpt k hk M A hM hA _ hfg).trans (mul_le_mul' le_rfl hg3))
  have h2 : eLpNorm g p volume ≤ eLpNorm f p volume + ENNReal.ofReal δ := by
    have : g = f - (f - g) := by abel
    rw [this]
    exact (eLpNorm_sub_le hf.1 hfg.1 hp).trans (add_le_add le_rfl hg3)
  calc eLpNorm (kernelOp k f) p volume
      ≤ D * (eLpNorm f p volume + ENNReal.ofReal δ) + L * ENNReal.ofReal δ :=
        h1.trans (add_le_add (mul_le_mul' le_rfl h2) le_rfl)
    _ = D * eLpNorm f p volume + (D + L) * ENNReal.ofReal δ := by ring
    _ ≤ D * eLpNorm f p volume + ε := by
        refine add_le_add le_rfl ?_
        rw [← ENNReal.ofReal_toReal hDt, ← ENNReal.ofReal_toReal hLt,
          ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal]
        apply ENNReal.ofReal_le_ofReal
        rw [hδ, mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ ε := ε.2
        nlinarith only [this, ENNReal.toReal_nonneg (a := D), ENNReal.toReal_nonneg (a := L)]

end Ops

variable {m : ℕ}

/-! ## The cutoffs -/

lemma betaB_ne_zero {t : ℝ} (h : betaB t ≠ 0) : 1 / 2 < t ∧ t < 5 / 2 := by
  have h' : t ∈ Function.support betaB := h
  rw [betaB.support_eq] at h'
  change t ∈ ball (3 / 2 : ℝ) 1 at h'
  rw [mem_ball, Real.dist_eq, abs_lt] at h'
  constructor <;> linarith [h'.1, h'.2]

lemma gamB_ne_zero {v : E m} (h : gamB m v ≠ 0) : ‖v‖ < 4 := by
  have h' : v ∈ Function.support (gamB m) := h
  rw [(gamB m).support_eq] at h'
  change v ∈ ball (0 : E m) 4 at h'
  simpa using h'

lemma thY_ne_zero {Y : E (m + 1)} (h : thetaY m Y ≠ 0) : ‖Y‖ < 2 := by
  have h' : Y ∈ Function.support (thY m) := h
  rw [(thY m).support_eq] at h'
  change Y ∈ ball (0 : E (m + 1)) 2 at h'
  simpa using h'

lemma abs_psiX_le (X : E (m + 1)) : |psiX m X| ≤ 1 := by
  unfold psiX
  rw [abs_mul, abs_of_nonneg (betaB.nonneg), abs_of_nonneg ((gamB m).nonneg)]
  exact mul_le_one₀ betaB.le_one ((gamB m).nonneg) (gamB m).le_one

lemma abs_thetaY_le (Y : E (m + 1)) : |thetaY m Y| ≤ 1 := by
  unfold thetaY
  rw [abs_of_nonneg ((thY m).nonneg)]
  exact (thY m).le_one

lemma psiX_continuous : Continuous (psiX m) := by
  unfold psiX
  exact (betaB.continuous.comp (vert_contDiff (m := m)).continuous).mul
    ((gamB m).continuous.comp (horiz_contDiff (m := m)).continuous)

lemma thetaY_continuous : Continuous (thetaY m) := (thY m).continuous

lemma thetaY_contDiff : ContDiff ℝ (⊤ : ℕ∞) (thetaY m) := (thY m).contDiff

/-! ## The kernel `T_R` -/

lemma Tker_continuous (δ : ℝ) (hK : Continuous (Kp m δ)) (R : ℝ) :
    Continuous (Function.uncurry (Tker m δ R)) := by
  have h1 := (psiX_continuous (m := m))
  have h2 := (thetaY_continuous (m := m))
  unfold Tker Function.uncurry
  fun_prop

lemma norm_Tker_le (δ M : ℝ) (hM : ∀ z, ‖Kp m δ z‖ ≤ M) (R : ℝ) (X Y : E (m + 1)) :
    ‖Tker m δ R X Y‖ ≤ M := by
  rw [Tker, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have h1 := abs_psiX_le X; have h2 := abs_thetaY_le Y
  have h3 := hM (R ^ 2 • X - R • Y)
  have h4 : |psiX m X| * |thetaY m Y| ≤ 1 := mul_le_one₀ h1 (abs_nonneg _) h2
  exact (mul_le_mul h4 h3 (norm_nonneg _) zero_le_one).trans (one_mul M).le

lemma Tker_supp (δ R : ℝ) {X Y : E (m + 1)} (h : Tker m δ R X Y ≠ 0) : ‖X‖ ≤ 7 ∧ ‖Y‖ ≤ 7 := by
  have h' : psiX m X * thetaY m Y ≠ 0 := by
    intro h0; apply h; simp [Tker, h0]
  have hψ : psiX m X ≠ 0 := left_ne_zero_of_mul h'
  have hθ : thetaY m Y ≠ 0 := right_ne_zero_of_mul h'
  have hb := betaB_ne_zero (left_ne_zero_of_mul hψ)
  have hg := gamB_ne_zero (right_ne_zero_of_mul hψ)
  have hy := thY_ne_zero hθ
  have hx := norm_le_horiz_add_vert X
  rw [abs_of_pos (by linarith [hb.1])] at hx
  constructor <;> linarith [hb.2]

/-- The substitution `y = R Y`. -/
lemma kernelOp_T_eq (δ : ℝ) (hδ : 0 < δ) (R : ℝ) (hR : 0 < R) (g : E (m + 1) → ℂ)
    (hs : 𝓢(E (m + 1), ℂ))
    (hhs : (hs : E (m + 1) → ℂ) = fun y => (thetaY m (R⁻¹ • y) : ℂ) * g (R⁻¹ • y))
    (X : E (m + 1)) :
    kernelOp (Tker m δ R) g X = ((psiX m X * (R ^ (m + 1))⁻¹ : ℝ) : ℂ) *
      parabolicBochnerRiesz (etaP m) δ (hs : E (m + 1) → ℂ) (R ^ 2 • X) := by
  rw [(kernel_rep m δ hδ).1 hs (R ^ 2 • X)]
  have hcs := Measure.integral_comp_smul (volume : Measure (E (m + 1)))
    (fun y => Kp m δ (R ^ 2 • X - y) * hs y) R
  rw [finrank_euclideanSpace_fin, abs_of_pos (by positivity)] at hcs
  simp only [hhs, inv_smul_smul₀ hR.ne'] at hcs
  rw [hhs]
  have hL : kernelOp (Tker m δ R) g X =
      (psiX m X : ℂ) * ∫ z, Kp m δ (R ^ 2 • X - R • z) * ((thetaY m z : ℂ) * g z) := by
    rw [kernelOp, ← integral_const_mul]
    congr 1; funext z; simp only [Tker]; push_cast; ring
  rw [hL, hcs, Complex.real_smul]
  push_cast
  ring

theorem opNorm_T_le (m : ℕ) (hm : 1 ≤ m) (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤) (δ : ℝ)
    (hδ : 0 < δ)
    (hPBR : ∃ C : ℝ≥0, ∀ f : 𝓢(E (m + 1), ℂ),
      eLpNorm (parabolicBochnerRiesz (etaP m) δ (f : E (m + 1) → ℂ)) p volume ≤
        C * eLpNorm f p volume) :
    ∃ C₀ : ℝ≥0, ∀ R : ℝ, 1 ≤ R → opNorm p p (kernelOp (Tker m δ R)) ≤
      C₀ * ENNReal.ofReal (R ^ (-(((m : ℝ) + 1) + ((m : ℝ) + 1) / p.toReal))) := by
  obtain ⟨-, hcont, ⟨M, hM⟩, -⟩ := kernel_rep m δ hδ
  obtain ⟨C, hC⟩ := hPBR
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne'
  refine ⟨C, fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  apply opNorm_le_of_schwartz p hp hpt (Tker m δ R) (Tker_continuous δ hcont R) M 7
    (norm_Tker_le δ M hM R) (fun X Y h => Tker_supp δ R h) _
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
  intro g
  set h : E (m + 1) → ℂ := fun y => (thetaY m (R⁻¹ • y) : ℂ) * g (R⁻¹ • y) with hhdef
  have htc : HasCompactSupport (fun y : E (m + 1) => (thetaY m (R⁻¹ • y) : ℂ)) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : E (m + 1)) (2 * R))
    intro y hy
    by_contra h0
    have h0' : thetaY m (R⁻¹ • y) ≠ 0 := fun e => h0 (by simp [e])
    have hz := thY_ne_zero h0'
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR0), inv_mul_lt_iff₀ hR0] at hz
    exact hy (by simp only [mem_closedBall, dist_zero_right]; linarith)
  have hhc : HasCompactSupport h := htc.mul_right
  have hhs : ContDiff ℝ (⊤ : ℕ∞) h :=
    (Complex.ofRealCLM.contDiff.comp (thetaY_contDiff.comp (contDiff_const_smul R⁻¹))).mul
      ((g.smooth ⊤).comp (contDiff_const_smul R⁻¹))
  set hs : 𝓢(E (m + 1), ℂ) := hhc.toSchwartzMap hhs
  have hcoe : (hs : E (m + 1) → ℂ) = h := rfl
  set S := parabolicBochnerRiesz (etaP m) δ (hs : E (m + 1) → ℂ) with hS
  set q := p.toReal with hq
  have h1 : eLpNorm (kernelOp (Tker m δ R) g) p volume ≤
      ENNReal.ofReal ((R ^ (m + 1))⁻¹) * eLpNorm (fun X => S (R ^ 2 • X)) p volume := by
    calc eLpNorm (kernelOp (Tker m δ R) g) p volume
        ≤ eLpNorm ((((R ^ (m + 1))⁻¹ : ℝ) : ℂ) • fun X => S (R ^ 2 • X)) p volume := by
          apply eLpNorm_mono
          intro X
          rw [kernelOp_T_eq δ hδ R hR0 g hs hcoe X, Pi.smul_apply, smul_eq_mul, norm_mul,
            norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, abs_mul]
          have := abs_psiX_le X
          have h0 : 0 ≤ ‖(((R ^ (m + 1))⁻¹ : ℝ))‖ * ‖S (R ^ 2 • X)‖ := by positivity
          rw [Real.norm_eq_abs] at h0 ⊢
          rw [mul_assoc]; exact mul_le_of_le_one_left h0 this
      _ = ENNReal.ofReal ((R ^ (m + 1))⁻¹) * eLpNorm (fun X => S (R ^ 2 • X)) p volume := by
          rw [eLpNorm_const_smul, ← ofReal_norm, Complex.norm_real,
            Real.norm_of_nonneg (by positivity)]
  have h2 := eLpNorm_comp_smul p hp0 hpt S (R ^ 2) (by positivity)
  have h3 : eLpNorm S p volume ≤ C * eLpNorm h p volume := hC hs
  have h4 : eLpNorm h p volume ≤ eLpNorm (fun y => g (R⁻¹ • y)) p volume := by
    apply eLpNorm_mono
    intro y
    simp only [hhdef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_thetaY_le _)
  have h5 := eLpNorm_comp_smul p hp0 hpt (g : E (m + 1) → ℂ) R⁻¹ (inv_pos.2 hR0)
  have hreal : (R ^ (m + 1))⁻¹ * ((R ^ 2) ^ (-(((m + 1 : ℕ) : ℝ) / q)) * (R⁻¹) ^ (-(((m + 1 : ℕ) : ℝ) / q))) =
      R ^ (-(((m : ℝ) + 1) + ((m : ℝ) + 1) / q)) := by
    rw [Real.inv_rpow hR0.le, ← Real.rpow_neg hR0.le, ← Real.rpow_natCast R 2,
      ← Real.rpow_mul hR0.le, ← Real.rpow_natCast R (m + 1), ← Real.rpow_neg hR0.le,
      ← Real.rpow_add hR0, ← Real.rpow_add hR0]
    congr 1; push_cast; ring
  calc eLpNorm (kernelOp (Tker m δ R) g) p volume
      ≤ ENNReal.ofReal ((R ^ (m + 1))⁻¹) * (ENNReal.ofReal ((R ^ 2) ^ (-(((m + 1 : ℕ) : ℝ) / q))) *
          (C * (ENNReal.ofReal ((R⁻¹) ^ (-(((m + 1 : ℕ) : ℝ) / q))) * eLpNorm (g : E (m + 1) → ℂ) p volume))) := by
        refine h1.trans ?_
        rw [h2]
        gcongr
        rw [← h5]
        exact h3.trans (by gcongr)
    _ = C * ENNReal.ofReal ((R ^ (m + 1))⁻¹ * ((R ^ 2) ^ (-(((m + 1 : ℕ) : ℝ) / q)) * (R⁻¹) ^ (-(((m + 1 : ℕ) : ℝ) / q)))) *
          eLpNorm (g : E (m + 1) → ℂ) p volume := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]; ring
    _ = _ := by rw [hreal]


end TaoBR.PBR.PartT

end S_PBRPartT

namespace TaoBR.PBR
alias opNorm_T_le := TaoBR.PBR.PartT.opNorm_T_le
end TaoBR.PBR

section S_PBRPartM

/-! # Part M: `opNorm_M_le` -/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace

namespace TaoBR.PBR.PartM

open TaoBR.PBR TaoBR.Parab

/-! ## Kernel operators (adapted from Part T: measurable instead of continuous kernels) -/

section Ops

variable {n : ℕ}

lemma kernelOp_aesm (k : E n → E n → ℂ) (hk : Measurable (Function.uncurry k)) (u : E n → ℂ)
    (hu : AEStronglyMeasurable u volume) : AEStronglyMeasurable (kernelOp k u) volume := by
  have h : AEStronglyMeasurable (fun z : E n × E n => k z.1 z.2 * u z.2)
      ((volume : Measure (E n)).prod volume) :=
    hk.aestronglyMeasurable.mul hu.comp_snd
  exact h.integral_prod_right'

lemma kernelOp_integrable (p : ℝ≥0∞) (hp : 1 ≤ p) (k : E n → E n → ℂ)
    (hk : Measurable (Function.uncurry k)) (M A : ℝ) (hM : ∀ x y, ‖k x y‖ ≤ M)
    (hA : ∀ x y, k x y ≠ 0 → ‖x‖ ≤ A ∧ ‖y‖ ≤ A) (u : E n → ℂ) (hu : MemLp u p volume)
    (x : E n) : Integrable (fun y => k x y * u y) volume := by
  have : IsFiniteMeasure (volume.restrict (closedBall (0 : E n) A)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have hu1 : Integrable u (volume.restrict (closedBall (0 : E n) A)) :=
    (hu.restrict _).integrable hp
  have hk1 : Measurable (k x) := hk.comp measurable_prodMk_left
  have h2 : IntegrableOn (fun y => k x y * u y) (closedBall (0 : E n) A) volume :=
    hu1.bdd_mul hk1.aestronglyMeasurable.restrict (ae_of_all _ (hM x))
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h2
  intro y hy
  have : k x y ≠ 0 := left_ne_zero_of_mul hy
  simpa using (hA x y this).2

lemma kernelOp_bound (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤) (k : E n → E n → ℂ)
    (M A : ℝ) (hM : ∀ x y, ‖k x y‖ ≤ M)
    (hA : ∀ x y, k x y ≠ 0 → ‖x‖ ≤ A ∧ ‖y‖ ≤ A) (u : E n → ℂ) (hu : MemLp u p volume) :
    eLpNorm (kernelOp k u) p volume ≤
      (ENNReal.ofReal M * volume (closedBall (0 : E n) A) ^ (1 - 1 / p.toReal) *
        volume (closedBall (0 : E n) A) ^ (1 / p.toReal)) * eLpNorm u p volume := by
  set B := closedBall (0 : E n) A
  have hp1 : 1 ≤ p.toReal := by
    have := (ENNReal.toReal_le_toReal (by simp) hpt).2 hp; simpa using this
  set c : ℝ≥0∞ := ENNReal.ofReal M * (eLpNorm u p volume * volume B ^ (1 - 1 / p.toReal))
  have hct : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
    hu.eLpNorm_ne_top (ENNReal.rpow_ne_top_of_nonneg (by
      have : 1 / p.toReal ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
      linarith) measure_closedBall_lt_top.ne))
  have hpt' : ∀ x, ‖kernelOp k u x‖ₑ ≤ ‖B.indicator (fun _ => c.toReal) x‖ₑ := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hct]
      calc ‖kernelOp k u x‖ₑ ≤ ∫⁻ y, ‖k x y * u y‖ₑ := enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ y, B.indicator (fun y => ENNReal.ofReal M * ‖u y‖ₑ) y := by
          apply lintegral_mono; intro y
          by_cases hy : y ∈ B
          · rw [Set.indicator_of_mem hy]
            show ‖k x y * u y‖ₑ ≤ _
            rw [enorm_mul]
            gcongr
            rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hM x y)
          · rw [Set.indicator_of_notMem hy]
            have : k x y = 0 := by
              by_contra h; exact hy (by simpa [B] using (hA x y h).2)
            simp [this]
        _ = ENNReal.ofReal M * ∫⁻ y in B, ‖u y‖ₑ := by
          rw [lintegral_indicator measurableSet_closedBall, lintegral_const_mul' _ _
            ENNReal.ofReal_ne_top]
        _ ≤ c := by
          simp only [c]
          gcongr
          have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict B)
            (p := 1) (q := p) hp hu.aestronglyMeasurable.restrict
          rw [eLpNorm_one_eq_lintegral_enorm, Measure.restrict_apply_univ] at h1
          refine h1.trans ?_
          simp only [ENNReal.toReal_one, div_one]
          gcongr
          exact Measure.restrict_le_self
    · have : kernelOp k u x = 0 := by
        simp only [kernelOp]
        apply integral_eq_zero_of_ae; apply ae_of_all; intro y
        have : k x y = 0 := by
          by_contra h; exact hx (by simpa [B] using (hA x y h).1)
        simp [this]
      simp [this]
  refine (eLpNorm_mono_enorm hpt').trans ((eLpNorm_indicator_const_le _ p).trans ?_)
  rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hct]
  simp only [c]
  apply le_of_eq; ring

/-- From an operator-norm bound to the inequality on a single `Lᵖ` function (Part V). -/
lemma eLpNorm_le_opNorm {p : ℝ≥0∞} {T : (E n → ℂ) → (E n → ℂ)} {D : ℝ≥0∞}
    (hT : opNorm p p T ≤ D) (hD : D ≠ ⊤) {f : E n → ℂ} (hf : MemLp f p volume) :
    eLpNorm (T f) p volume ≤ D * eLpNorm f p volume := by
  have hlt : sInf {C : ℝ≥0∞ | ∀ f : E n → ℂ, MemLp f p volume →
      eLpNorm (T f) p volume ≤ C * eLpNorm f p volume} < ⊤ :=
    lt_of_le_of_lt hT (lt_top_iff_ne_top.2 hD)
  obtain ⟨C₁, hC₁, -⟩ := sInf_lt_iff.1 hlt
  by_cases hz : eLpNorm f p volume = 0
  · have := hC₁ f hf; rw [hz, mul_zero] at this; rw [hz, mul_zero]; exact this
  have hft : eLpNorm f p volume ≠ ⊤ := hf.eLpNorm_ne_top
  have : eLpNorm (T f) p volume / eLpNorm f p volume ≤ opNorm p p T := by
    apply le_sInf
    intro C hC
    exact (ENNReal.div_le_iff hz hft).2 (hC f hf)
  exact (ENNReal.div_le_iff hz hft).1 (this.trans hT)

end Ops

variable {m : ℕ}

/-! ## `ex`, coordinates, cutoffs -/

lemma norm_ex (t : ℝ) : ‖ex t‖ = 1 := by
  rw [ex, show 2 * Real.pi * Complex.I * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

lemma ex_contDiff : ContDiff ℝ (⊤ : ℕ∞) ex := by
  unfold ex
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

lemma vert_sub_smul (X Y : E (m + 1)) (τ : ℝ) :
    vert (X - τ • Y) = vert X - τ * vert Y := by
  simp [vert]

lemma horiz_smul (c : ℝ) (X : E (m + 1)) : horiz (c • X) = c • horiz X := by
  ext i; simp

lemma vert_smul (c : ℝ) (X : E (m + 1)) : vert (c • X) = c * vert X := by
  simp [vert]

lemma abs_vert_le (Y : E (m + 1)) : |vert Y| ≤ ‖Y‖ := by
  have := norm_sq_hv Y
  have h : |vert Y| ^ 2 ≤ ‖Y‖ ^ 2 := by rw [sq_abs]; nlinarith [sq_nonneg ‖horiz Y‖]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).1 h

lemma region {X Y : E (m + 1)} (h : psiX m X * thetaY m Y ≠ 0) :
    ‖horiz X‖ < 4 ∧ 1 / 2 < vert X ∧ vert X < 5 / 2 ∧ ‖Y‖ < 2 := by
  have h1 : betaB (vert X) ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul h)
  have h2 : gamB m (horiz X) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  have h3 : thY m Y ≠ 0 := right_ne_zero_of_mul h
  have g1 : vert X ∈ Function.support betaB := h1
  have g2 : horiz X ∈ Function.support (gamB m) := h2
  have g3 : Y ∈ Function.support (thY m) := h3
  rw [ContDiffBump.support_eq] at g1 g2 g3
  simp only [mem_ball, Real.dist_eq, dist_zero_right, betaB, gamB, thY] at g1 g2 g3
  rw [abs_lt] at g1
  refine ⟨g2, by linarith, by linarith, g3⟩

lemma supp7 {X Y : E (m + 1)} (h : psiX m X * thetaY m Y ≠ 0) : ‖X‖ ≤ 7 ∧ ‖Y‖ ≤ 7 := by
  obtain ⟨hA, hx1, hx2, hY⟩ := region h
  have hX := norm_le_horiz_add_vert X
  rw [abs_of_pos (by linarith)] at hX
  constructor <;> linarith

alias abs_psiX_le := TaoBR.PBR.PartT.abs_psiX_le

lemma abs_thetaY_le (Y : E (m + 1)) : |thetaY m Y| ≤ 1 := by
  unfold thetaY
  rw [abs_of_nonneg ((thY m).nonneg)]; exact (thY m).le_one

/-! ## The kernels `T_R` and `M_R` -/

alias Tker_continuous := TaoBR.PBR.PartT.Tker_continuous

alias norm_Tker_le := TaoBR.PBR.PartT.norm_Tker_le

lemma Mker_measurable (δ : ℝ) (F : E m → ℝ → ℂ) (hF : Continuous (Function.uncurry F)) (R : ℝ) :
    Measurable (Function.uncurry (Mker m δ F R)) := by
  have hv : Continuous (fun ξ : E (m + 1) => vert ξ) := vert_contDiff.continuous
  have hh : Continuous (fun ξ : E (m + 1) => horiz ξ) := horiz_contDiff.continuous
  have hW : Continuous (fun p : E (m + 1) × E (m + 1) => p.1 - R⁻¹ • p.2) := by fun_prop
  have hwv : Measurable (fun p : E (m + 1) × E (m + 1) => vert (p.1 - R⁻¹ • p.2)) :=
    (hv.comp hW).measurable
  have hwh : Continuous (fun p : E (m + 1) × E (m + 1) => horiz (p.1 - R⁻¹ • p.2)) := hh.comp hW
  have hψ : Continuous (fun p : E (m + 1) × E (m + 1) => psiX m p.1) := by
    unfold psiX
    exact (betaB.continuous.comp (hv.comp continuous_fst)).mul
      ((gamB m).continuous.comp (hh.comp continuous_fst))
  have hθ : Continuous (fun p : E (m + 1) × E (m + 1) => thetaY m p.2) := by
    unfold thetaY; exact (thY m).continuous.comp continuous_snd
  have hreal : Measurable (fun p : E (m + 1) × E (m + 1) =>
      psiX m p.1 * thetaY m p.2 * vert (p.1 - R⁻¹ • p.2) ^ (-gam m δ)) :=
    (hψ.measurable.mul hθ.measurable).mul (hwv.pow_const _)
  have hphi : Measurable (fun p : E (m + 1) × E (m + 1) => phiP (p.1 - R⁻¹ • p.2)) := by
    unfold phiP
    exact ((continuous_norm.comp hwh).pow 2).measurable.div (measurable_const.mul hwv)
  have hu : Measurable (fun p : E (m + 1) × E (m + 1) => uP (p.1 - R⁻¹ • p.2)) := by
    unfold uP
    exact hwv.inv.smul hwh.measurable
  have hσ : Measurable (fun p : E (m + 1) × E (m + 1) => R⁻¹ ^ 2 / vert (p.1 - R⁻¹ • p.2)) :=
    measurable_const.div hwv
  have hFc := hF.measurable.comp (hu.prodMk hσ)
  have hex : Measurable (fun p : E (m + 1) × E (m + 1) => ex (-(R ^ 2 * phiP (p.1 - R⁻¹ • p.2)))) :=
    ex_contDiff.continuous.measurable.comp (measurable_const.mul hphi).neg
  exact ((Complex.measurable_ofReal.comp hreal).mul hex).mul hFc

/-! ## Kernel asymptotics -/

/-- `‖χ‖₁`, a bound for `|E|`. -/
noncomputable def Ichi (m : ℕ) : ℝ := ∫ v : E m, |chiH m v|

lemma Ichi_nonneg : 0 ≤ Ichi m := integral_nonneg fun _ => abs_nonneg _

lemma norm_Efun_le (z : E (m + 1)) : ‖Efun m z‖ ≤ Ichi m := by
  unfold Efun Ichi
  refine (norm_integral_le_integral_norm _).trans
    (le_of_eq (integral_congr_ae (ae_of_all _ fun v => ?_)))
  simp only [norm_mul, norm_ex, mul_one, Complex.norm_real, Real.norm_eq_abs]

lemma kernel_asymp (δ : ℝ) (hδ : 0 < δ) (cB cE : ℂ) (g : ℝ → ℂ) (A : E m → ℝ → ℂ) (C K : ℝ)
    (hB : ∀ t : ℝ, 1 ≤ t → ‖Bfun δ t - cB * ((t ^ (-(δ + 1)) : ℝ) : ℂ) * g t⁻¹‖ ≤ C * t ^ (-K))
    (hE : ∀ z : E (m + 1), 0 < vert z →
      Efun m z = cE * ((vert z ^ (-((m : ℝ) / 2)) : ℝ) : ℂ) * ex (-phiP z) * A (uP z) (vert z)⁻¹)
    (z : E (m + 1)) (hz : 1 ≤ vert z) :
    ‖Kp m δ z - cB * cE * ((vert z ^ (-gam m δ) : ℝ) : ℂ) * ex (-phiP z) *
        (A (uP z) (vert z)⁻¹ * g (vert z)⁻¹)‖ ≤ C * vert z ^ (-K) * Ichi m := by
  have ht : 0 < vert z := by linarith
  rw [(kernel_rep m δ hδ).2.2.2 z]
  have hsplit : Bfun δ (vert z) * Efun m z - cB * cE * ((vert z ^ (-gam m δ) : ℝ) : ℂ) *
        ex (-phiP z) * (A (uP z) (vert z)⁻¹ * g (vert z)⁻¹) =
      (Bfun δ (vert z) - cB * ((vert z ^ (-(δ + 1)) : ℝ) : ℂ) * g (vert z)⁻¹) * Efun m z := by
    have hg : vert z ^ (-gam m δ) = vert z ^ (-(δ + 1)) * vert z ^ (-((m : ℝ) / 2)) := by
      rw [← Real.rpow_add ht]; congr 1; unfold gam; ring
    rw [hE z ht, hg]; push_cast; ring
  rw [hsplit, norm_mul]
  exact mul_le_mul (hB _ hz) (norm_Efun_le z) (norm_nonneg _) (le_trans (norm_nonneg _) (hB _ hz))

/-- The pointwise decomposition `T_R = c R^{-2γ} M_R + Err` with `|Err| ≤ C ‖χ‖₁ 4^K R^{-K}`. -/
lemma err_bound (δ : ℝ) (hδ : 0 < δ) (cB cE : ℂ) (g : ℝ → ℂ) (A : E m → ℝ → ℂ) (C K : ℝ)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hB : ∀ t : ℝ, 1 ≤ t → ‖Bfun δ t - cB * ((t ^ (-(δ + 1)) : ℝ) : ℂ) * g t⁻¹‖ ≤ C * t ^ (-K))
    (hE : ∀ z : E (m + 1), 0 < vert z →
      Efun m z = cE * ((vert z ^ (-((m : ℝ) / 2)) : ℝ) : ℂ) * ex (-phiP z) * A (uP z) (vert z)⁻¹)
    (R : ℝ) (hR : 8 ≤ R) (X Y : E (m + 1)) :
    ‖Tker m δ R X Y - cB * cE * ((R ^ (-(2 * gam m δ)) : ℝ) : ℂ) *
        Mker m δ (fun a σ => A a σ * g σ) R X Y‖ ≤ C * Ichi m * 4 ^ K * R ^ (-K) := by
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hI := Ichi_nonneg (m := m)
  by_cases h0 : psiX m X * thetaY m Y = 0
  · have h1 : Tker m δ R X Y = 0 := by simp [Tker, h0]
    have h2 : Mker m δ (fun a σ => A a σ * g σ) R X Y = 0 := by simp [Mker, h0]
    rw [h1, h2]; simp only [mul_zero, sub_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC hI) (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg hR0.le _)
  obtain ⟨-, hx1, -, hY⟩ := region h0
  set w := X - R⁻¹ • Y with hw
  have hRi : R⁻¹ ≤ 1 / 8 := by rw [one_div]; exact inv_anti₀ (by norm_num) hR
  have hvw : 1 / 4 ≤ vert w := by
    rw [hw, vert_sub_smul]
    have h1 := abs_vert_le Y
    have : R⁻¹ * vert Y ≤ 1 / 4 := by
      calc R⁻¹ * vert Y ≤ R⁻¹ * |vert Y| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.2 hR0.le)
        _ ≤ (1 / 8) * 2 :=
            mul_le_mul hRi (h1.trans hY.le) (abs_nonneg _) (by norm_num)
        _ = 1 / 4 := by norm_num
    linarith only [this, hx1]
  have hwp : 0 < vert w := lt_of_lt_of_le (by norm_num) hvw
  have hz : R ^ 2 • X - R • Y = R ^ 2 • w := by
    rw [hw, smul_sub, smul_smul, show R ^ 2 * R⁻¹ = R by field_simp]
  have hvz : vert (R ^ 2 • w) = R ^ 2 * vert w := vert_smul _ _
  have hhz : horiz (R ^ 2 • w) = R ^ 2 • horiz w := horiz_smul _ _
  have hzp : R / 4 ≤ vert (R ^ 2 • w) := by
    rw [hvz]
    calc R / 4 ≤ R ^ 2 * (1 / 4) := by nlinarith only [hR]
      _ ≤ R ^ 2 * vert w := mul_le_mul_of_nonneg_left hvw (sq_nonneg R)
  have hz1 : 1 ≤ vert (R ^ 2 • w) := by linarith only [hzp, hR]
  have hphi : phiP (R ^ 2 • w) = R ^ 2 * phiP w := by
    unfold phiP
    rw [hhz, hvz, norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  have hu : uP (R ^ 2 • w) = uP w := by
    unfold uP
    rw [hhz, hvz, smul_smul]; congr 1; field_simp
  have hσ : (vert (R ^ 2 • w))⁻¹ = R⁻¹ ^ 2 / vert w := by rw [hvz]; field_simp
  have hpow : R ^ (-(2 * gam m δ)) * vert w ^ (-gam m δ) = vert (R ^ 2 • w) ^ (-gam m δ) := by
    rw [hvz, Real.mul_rpow (by positivity) hwp.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hR0.le]
    congr 2; push_cast; ring
  have hid : Tker m δ R X Y - cB * cE * ((R ^ (-(2 * gam m δ)) : ℝ) : ℂ) *
        Mker m δ (fun a σ => A a σ * g σ) R X Y =
      ((psiX m X * thetaY m Y : ℝ) : ℂ) *
        (Kp m δ (R ^ 2 • w) - cB * cE * ((vert (R ^ 2 • w) ^ (-gam m δ) : ℝ) : ℂ) *
          ex (-phiP (R ^ 2 • w)) *
          (A (uP (R ^ 2 • w)) (vert (R ^ 2 • w))⁻¹ * g (vert (R ^ 2 • w))⁻¹)) := by
    unfold Tker Mker
    rw [hz, ← hw, hphi, hu, hσ, ← hpow]
    push_cast; ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hk := kernel_asymp δ hδ cB cE g A C K hB hE (R ^ 2 • w) hz1
  have hψθ : |psiX m X * thetaY m Y| ≤ 1 := by
    rw [abs_mul]; exact mul_le_one₀ (abs_psiX_le X) (abs_nonneg _) (abs_thetaY_le Y)
  have hr : vert (R ^ 2 • w) ^ (-K) ≤ 4 ^ K * R ^ (-K) := by
    calc vert (R ^ 2 • w) ^ (-K) ≤ (R / 4) ^ (-K) :=
          Real.rpow_le_rpow_of_nonpos (div_pos hR0 (by norm_num)) hzp (neg_nonpos.2 hK)
      _ = 4 ^ K * R ^ (-K) := by
          rw [Real.div_rpow hR0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
          field_simp
  calc |psiX m X * thetaY m Y| * ‖Kp m δ (R ^ 2 • w) - _‖
      ≤ 1 * (C * vert (R ^ 2 • w) ^ (-K) * Ichi m) :=
        mul_le_mul hψθ hk (norm_nonneg _) zero_le_one
    _ ≤ 1 * (C * (4 ^ K * R ^ (-K)) * Ichi m) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hC) hI)
          zero_le_one
    _ = C * Ichi m * 4 ^ K * R ^ (-K) := by ring

/-! ## The main term -/

theorem opNorm_M_le (m : ℕ) (hm : 1 ≤ m) (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤) (δ : ℝ)
    (hδ : 0 < δ) (C₀ : ℝ≥0)
    (hT : ∀ R : ℝ, 1 ≤ R → opNorm p p (kernelOp (Tker m δ R)) ≤
      C₀ * ENNReal.ofReal (R ^ (-(((m : ℝ) + 1) + ((m : ℝ) + 1) / p.toReal)))) :
    ∃ F : E m → ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) ∧
      (∀ a : E m, ‖a‖ ≤ 12 → F a 0 = 1) ∧
      ∃ C : ℝ≥0, ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → opNorm p p (kernelOp (Mker m δ F R)) ≤
        C * ENNReal.ofReal (R ^ (2 * δ + 1 - ((m : ℝ) + 1) / p.toReal)) := by
  obtain ⟨cB, hcB, g, hg, hg0, hB⟩ := Bfun_asymp δ hδ
  obtain ⟨cE, hcE, A, hA, hA0, hE⟩ := Efun_eq m hm
  obtain ⟨-, hKc, ⟨MK, hMK⟩, -⟩ := kernel_rep m δ hδ
  set q := p.toReal with hq
  have hq1 : 1 ≤ q := by
    have := (ENNReal.toReal_le_toReal (by simp) hpt).2 hp; simpa using this
  set K : ℝ := ((m : ℝ) + 1) + ((m : ℝ) + 1) / q with hKdef
  have hK : 0 ≤ K := by positivity
  obtain ⟨C, hC⟩ := hB K
  have hC0 : 0 ≤ C := by
    simpa using le_trans (norm_nonneg _) (hC 1 le_rfl)
  set F : E m → ℝ → ℂ := fun a σ => A a σ * g σ with hFdef
  have hFc : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) := by
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun q : E m × ℝ => g q.2) := hg.comp contDiff_snd
    exact hA.mul h2
  refine ⟨F, hFc, fun a ha => by
    simp [hFdef, hA0 a (ha.trans (by norm_num)), hg0], ?_⟩
  set c : ℂ := cB * cE with hc
  have hc0 : c ≠ 0 := mul_ne_zero hcB hcE
  set Cerr : ℝ := C * Ichi m * 4 ^ K with hCerr
  have hCerr0 : 0 ≤ Cerr := by have := Ichi_nonneg (m := m); positivity
  set V : ℝ≥0∞ := volume (closedBall (0 : E (m + 1)) 7) ^ (1 - 1 / q) *
    volume (closedBall (0 : E (m + 1)) 7) ^ (1 / q) with hV
  have hVt : V ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg ?_ measure_closedBall_lt_top.ne)
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_closedBall_lt_top.ne)
    have : 1 / q ≤ 1 := by rw [div_le_one (by linarith only [hq1])]; exact hq1
    linarith only [this]
  set D : ℝ := ‖c‖⁻¹ * (C₀ + Cerr * V.toReal) with hD
  have hD0 : 0 ≤ D := mul_nonneg (inv_nonneg.2 (norm_nonneg _))
    (add_nonneg (NNReal.coe_nonneg C₀) (mul_nonneg hCerr0 ENNReal.toReal_nonneg))
  refine ⟨D.toNNReal, 8, fun R hR => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  set a : ℂ := c * ((R ^ (-(2 * gam m δ)) : ℝ) : ℂ) with ha
  have hnorm : ‖a‖ = ‖c‖ * R ^ (-(2 * gam m δ)) := by
    rw [ha, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have ha0 : a ≠ 0 := by
    rw [ha]; exact mul_ne_zero hc0 (by exact_mod_cast (Real.rpow_pos_of_pos hR0 _).ne')
  set Err : E (m + 1) → E (m + 1) → ℂ := fun X Y => Tker m δ R X Y - a * Mker m δ F R X Y
    with hErr
  have hTm : Measurable (Function.uncurry (Tker m δ R)) := (Tker_continuous δ hKc R).measurable
  have hMm : Measurable (Function.uncurry (Mker m δ F R)) := Mker_measurable δ F hFc.continuous R
  have hErrM : Measurable (Function.uncurry Err) := hTm.sub (measurable_const.mul hMm)
  have hErrB : ∀ X Y, ‖Err X Y‖ ≤ Cerr * R ^ (-K) := fun X Y =>
    err_bound δ hδ cB cE g A C K hC0 hK hC hE R hR X Y
  have hS : ∀ X Y : E (m + 1), (Tker m δ R X Y ≠ 0 ∨ Err X Y ≠ 0) → ‖X‖ ≤ 7 ∧ ‖Y‖ ≤ 7 := by
    intro X Y h
    apply supp7
    intro h0
    have h0' : (psiX m X : ℂ) * (thetaY m Y : ℂ) = 0 := by exact_mod_cast h0
    rcases h with h | h <;> apply h <;> simp [hErr, Tker, Mker, h0']
  have hTS : ∀ X Y, Tker m δ R X Y ≠ 0 → ‖X‖ ≤ 7 ∧ ‖Y‖ ≤ 7 := fun X Y h => hS X Y (Or.inl h)
  have hES : ∀ X Y, Err X Y ≠ 0 → ‖X‖ ≤ 7 ∧ ‖Y‖ ≤ 7 := fun X Y h => hS X Y (Or.inr h)
  apply sInf_le
  intro f hf
  have hiT := kernelOp_integrable p hp (Tker m δ R) hTm MK 7 (norm_Tker_le δ MK hMK R) hTS f hf
  have hiE := kernelOp_integrable p hp Err hErrM _ 7 hErrB hES f hf
  have hsplit : kernelOp (Mker m δ F R) f =
      a⁻¹ • (kernelOp (Tker m δ R) f - kernelOp Err f) := by
    funext X
    simp only [kernelOp, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← integral_sub (hiT X) (hiE X), ← integral_const_mul]
    congr 1; funext Y
    simp only [hErr]
    field_simp
    ring
  have h1 : eLpNorm (kernelOp (Tker m δ R) f) p volume ≤
      (C₀ * ENNReal.ofReal (R ^ (-K))) * eLpNorm f p volume :=
    eLpNorm_le_opNorm (hT R (by linarith only [hR])) (ENNReal.mul_ne_top ENNReal.coe_ne_top
      ENNReal.ofReal_ne_top) hf
  have h2 : eLpNorm (kernelOp Err f) p volume ≤
      (ENNReal.ofReal (Cerr * R ^ (-K)) * V) * eLpNorm f p volume := by
    have := kernelOp_bound p hp hpt Err _ 7 hErrB hES f hf
    rw [hV, ← mul_assoc]; exact this
  have hexp : (R ^ (-(2 * gam m δ)))⁻¹ * R ^ (-K) = R ^ (2 * δ + 1 - ((m : ℝ) + 1) / q) := by
    rw [← Real.rpow_neg hR0.le, neg_neg, ← Real.rpow_add hR0]
    congr 1; rw [hKdef]; unfold gam; ring
  rw [hsplit, eLpNorm_const_smul]
  calc ‖a⁻¹‖ₑ * eLpNorm (kernelOp (Tker m δ R) f - kernelOp Err f) p volume
      ≤ ‖a⁻¹‖ₑ * (eLpNorm (kernelOp (Tker m δ R) f) p volume + eLpNorm (kernelOp Err f) p volume) := by
        exact mul_le_mul_right
          (eLpNorm_sub_le (kernelOp_aesm _ hTm f hf.1) (kernelOp_aesm _ hErrM f hf.1) hp) _
    _ ≤ ‖a⁻¹‖ₑ * ((C₀ * ENNReal.ofReal (R ^ (-K))) * eLpNorm f p volume +
          (ENNReal.ofReal (Cerr * R ^ (-K)) * V) * eLpNorm f p volume) :=
        mul_le_mul_right (add_le_add h1 h2) _
    _ = ENNReal.ofReal (‖a‖⁻¹ * (C₀ * R ^ (-K) + Cerr * R ^ (-K) * V.toReal)) *
          eLpNorm f p volume := by
        have hRK : 0 ≤ R ^ (-K) := Real.rpow_nonneg hR0.le _
        rw [ENNReal.ofReal_mul (p := ‖a‖⁻¹) (inv_nonneg.2 (norm_nonneg _)),
          ENNReal.ofReal_add (mul_nonneg (NNReal.coe_nonneg C₀) hRK)
            (mul_nonneg (mul_nonneg hCerr0 hRK) (ENNReal.toReal_nonneg (a := V))),
          ENNReal.ofReal_mul (p := (C₀ : ℝ)) (NNReal.coe_nonneg C₀),
          ENNReal.ofReal_mul (p := Cerr * R ^ (-K)) (mul_nonneg hCerr0 hRK),
          ENNReal.ofReal_toReal hVt, ENNReal.ofReal_coe_nnreal, ← norm_inv, ofReal_norm]
        ring
    _ = ENNReal.ofReal (D * R ^ (2 * δ + 1 - ((m : ℝ) + 1) / q)) * eLpNorm f p volume := by
        congr 2
        rw [hnorm, ← hexp, hD, mul_inv]; ring
    _ = ↑D.toNNReal * ENNReal.ofReal (R ^ (2 * δ + 1 - ((m : ℝ) + 1) / q)) *
          eLpNorm f p volume := by
        rw [ENNReal.ofReal_mul hD0]; rfl


end TaoBR.PBR.PartM

end S_PBRPartM

namespace TaoBR.PBR
alias opNorm_M_le := TaoBR.PBR.PartM.opNorm_M_le
end TaoBR.PBR

section S_PBRPartL

/-! # Part L: `opNorm_L_le` (Lemma 2.1 applied to the main term) -/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace

namespace TaoBR.PBR

open Parab

namespace PartL

variable {m : ℕ}

/-! ## Smooth surrogates -/

/-- A globally smooth function `≥ 1/8`, equal to `t` for `t ≥ 1/4`. -/
noncomputable def uPos (t : ℝ) : ℝ := 1 / 8 + (t - 1 / 8) * Real.smoothTransition (8 * t - 1)

lemma uPos_of_ge {t : ℝ} (h : 1 / 4 ≤ t) : uPos t = t := by
  rw [uPos, Real.smoothTransition.one_of_one_le (by linarith)]; ring

lemma uPos_ge (t : ℝ) : 1 / 8 ≤ uPos t := by
  unfold uPos
  rcases le_or_gt (1 / 8) t with h | h
  · have := Real.smoothTransition.nonneg (8 * t - 1)
    nlinarith
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; norm_num

lemma uPos_pos (t : ℝ) : 0 < uPos t := lt_of_lt_of_le (by norm_num) (uPos_ge t)

lemma uPos_contDiff : ContDiff ℝ (⊤ : ℕ∞) uPos := by
  unfold uPos
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)))

/-- A globally smooth surrogate for `z ↦ z⁻¹`, exact for `|z| ≥ 1/2`. -/
noncomputable def invS (z : ℂ) : ℂ := ((uPos (‖z‖ ^ 2))⁻¹ : ℝ) • (starRingEnd ℂ) z

lemma invS_contDiff : ContDiff ℝ (⊤ : ℕ∞) invS := by
  unfold invS
  exact ((uPos_contDiff.comp (contDiff_norm_sq ℝ)).inv fun z => (uPos_pos _).ne').smul
    Complex.conjCLE.contDiff

lemma invS_eq {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) : invS z = z⁻¹ := by
  rw [invS, uPos_of_ge (by nlinarith), Complex.inv_def, Complex.normSq_eq_norm_sq,
    Complex.real_smul, mul_comm]

/-! ## `ex` -/

lemma ex_add (s t : ℝ) : ex (s + t) = ex s * ex t := by
  unfold ex; rw [← Complex.exp_add]; push_cast; ring_nf

alias norm_ex := TaoBR.PBR.PartM.norm_ex

lemma ex_contDiff : ContDiff ℝ (⊤ : ℕ∞) ex := by
  unfold ex
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

/-! ## Coordinates -/

lemma horiz_sub_smul (X Y : E (m + 1)) (τ : ℝ) :
    horiz (X - τ • Y) = horiz X - τ • horiz Y := by
  ext i; simp

lemma vert_sub_smul (X Y : E (m + 1)) (τ : ℝ) :
    vert (X - τ • Y) = vert X - τ * vert Y := by
  simp [vert]

lemma inner_graphPt (v : E m) (Y : E (m + 1)) :
    ⟪graphPt v, Y⟫ = ⟪v, horiz Y⟫ + ‖v‖ ^ 2 / 2 * vert Y := by
  simp only [graphPt, mkPoint, PiLp.inner_apply, Fin.sum_univ_castSucc]
  simp [vert, horiz, mul_comm]

lemma norm_horiz_le (Y : E (m + 1)) : ‖horiz Y‖ ≤ ‖Y‖ := by
  have := norm_sq_hv Y
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by nlinarith)

alias abs_vert_le := TaoBR.PBR.PartM.abs_vert_le

/-! ## The phase identity -/

lemma phase_alg (R x y w A2 AB B2 W2 : ℝ) (hR : R ≠ 0) (hx : x ≠ 0) (hw : w ≠ 0)
    (hwd : w = x - R⁻¹ * y) (hW2 : W2 = A2 - 2 * R⁻¹ * AB + R⁻¹ ^ 2 * B2) :
    R ^ 2 * (W2 / (2 * w)) = R ^ 2 * (A2 / (2 * x)) + R * (-(x⁻¹ * AB) + x⁻¹ ^ 2 * A2 / 2 * y) +
      (x ^ 2 * B2 - 2 * x * y * AB + y ^ 2 * A2) / (2 * x ^ 2 * w) := by
  subst hW2
  have hw' : R * w = R * x - y := by rw [hwd]; field_simp
  field_simp
  linear_combination (-A2 * y + 2 * AB * x - R * A2 * x) * hw'

lemma phase_id (R : ℝ) (hR : R ≠ 0) (X Y : E (m + 1)) (hx : vert X ≠ 0)
    (hw : vert (X - R⁻¹ • Y) ≠ 0) :
    R ^ 2 * phiP (X - R⁻¹ • Y) = R ^ 2 * phiP X + R * ⟪graphPt (-uP X), Y⟫ +
      (vert X ^ 2 * ‖horiz Y‖ ^ 2 - 2 * vert X * vert Y * ⟪horiz X, horiz Y⟫ +
        vert Y ^ 2 * ‖horiz X‖ ^ 2) / (2 * vert X ^ 2 * vert (X - R⁻¹ • Y)) := by
  rw [inner_graphPt, phiP, phiP, uP, norm_neg, inner_neg_left, inner_smul_left, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [conj_trivial]
  apply phase_alg R (vert X) (vert Y) _ _ _ _ _ hR hx hw (vert_sub_smul X Y R⁻¹)
  rw [horiz_sub_smul, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs]; ring


/-! ## Cutoffs -/

alias region := TaoBR.PBR.PartM.region

alias abs_psiX_le := TaoBR.PBR.PartM.abs_psiX_le

lemma abs_thetaY_le (Y : E (m + 1)) : |thetaY m Y| ≤ 1 := by
  unfold thetaY
  rw [abs_of_nonneg ((thY m).nonneg)]; exact (thY m).le_one

/-- The cutoff on `((X, τ), Y)`: `1` on `closedBall 0 10`, supported in `ball 0 20`. -/
noncomputable def cutB (m : ℕ) : ContDiffBump (0 : (E (m + 1) × ℝ) × E (m + 1)) :=
  ⟨10, 20, by norm_num, by norm_num⟩

/-- The phase error `a(X, Y, τ) = |XₙY̲ - YₙX̲|² / (2 Xₙ² wₙ)` with smooth surrogates. -/
noncomputable def aS (X Y : E (m + 1)) (τ : ℝ) : ℝ :=
  (vert X ^ 2 * ‖horiz Y‖ ^ 2 - 2 * vert X * vert Y * ⟪horiz X, horiz Y⟫ +
    vert Y ^ 2 * ‖horiz X‖ ^ 2) / (2 * uPos (vert X) ^ 2 * uPos (vert (X - τ • Y)))

/-- The Lemma 2.1 multiplier `b = e(a) Xₙ^{-γ} / (wₙ^{-γ} F(u(w), τ²/wₙ))`, smoothed and cut off. -/
noncomputable def bL (δ : ℝ) (F : E m → ℝ → ℂ) (X Y : E (m + 1)) (τ : ℝ) : ℂ :=
  ((cutB m ((X, τ), Y) * uPos (vert X) ^ (-gam m δ) * uPos (vert (X - τ • Y)) ^ gam m δ : ℝ) : ℂ) *
    ex (aS X Y τ) *
    invS (F ((uPos (vert (X - τ • Y)))⁻¹ • horiz (X - τ • Y)) (τ ^ 2 / uPos (vert (X - τ • Y))))

lemma bL_contDiff (δ : ℝ) (F : E m → ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w : (E (m + 1) × ℝ) × E (m + 1) => bL δ F w.1.1 w.2 w.1.2) := by
  have hX : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E (m + 1) × ℝ) × E (m + 1) => w.1.1) :=
    contDiff_fst.comp contDiff_fst
  have hT : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E (m + 1) × ℝ) × E (m + 1) => w.1.2) :=
    contDiff_snd.comp contDiff_fst
  have hY : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E (m + 1) × ℝ) × E (m + 1) => w.2) := contDiff_snd
  have hW : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E (m + 1) × ℝ) × E (m + 1) => w.1.1 - w.1.2 • w.2) :=
    hX.sub (hT.smul hY)
  have hxv := vert_contDiff.comp hX
  have hyv := vert_contDiff.comp hY
  have hxh := horiz_contDiff.comp hX
  have hyh := horiz_contDiff.comp hY
  have hPx : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E (m + 1) × ℝ) × E (m + 1) => uPos (vert w.1.1)) :=
    uPos_contDiff.comp hxv
  have hPw : ContDiff ℝ (⊤ : ℕ∞)
      (fun w : (E (m + 1) × ℝ) × E (m + 1) => uPos (vert (w.1.1 - w.1.2 • w.2))) :=
    uPos_contDiff.comp (vert_contDiff.comp hW)
  have hcut : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E (m + 1) × ℝ) × E (m + 1) => cutB m w) :=
    (cutB m).contDiff
  have hreal : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E (m + 1) × ℝ) × E (m + 1) =>
      cutB m ((w.1.1, w.1.2), w.2) * uPos (vert w.1.1) ^ (-gam m δ) *
        uPos (vert (w.1.1 - w.1.2 • w.2)) ^ gam m δ) :=
    (hcut.mul (hPx.rpow_const_of_ne fun w => (uPos_pos _).ne')).mul
      (hPw.rpow_const_of_ne fun w => (uPos_pos _).ne')
  have haS : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E (m + 1) × ℝ) × E (m + 1) => aS w.1.1 w.2 w.1.2) := by
    unfold aS
    refine ContDiff.div ?_ ((contDiff_const.mul (hPx.pow 2)).mul hPw) fun w => ?_
    · exact ((hxv.pow 2).mul ((contDiff_norm_sq ℝ).comp hyh)).sub
        (((contDiff_const.mul hxv).mul hyv).mul (hxh.inner ℝ hyh)) |>.add
        ((hyv.pow 2).mul ((contDiff_norm_sq ℝ).comp hxh))
    · have := uPos_pos (vert w.1.1); have := uPos_pos (vert (w.1.1 - w.1.2 • w.2)); positivity
  have hu : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E (m + 1) × ℝ) × E (m + 1) =>
      (uPos (vert (w.1.1 - w.1.2 • w.2)))⁻¹ • horiz (w.1.1 - w.1.2 • w.2)) :=
    (hPw.inv fun w => (uPos_pos _).ne').smul (horiz_contDiff.comp hW)
  have hσ : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E (m + 1) × ℝ) × E (m + 1) =>
      w.1.2 ^ 2 / uPos (vert (w.1.1 - w.1.2 • w.2))) :=
    (hT.pow 2).div hPw fun w => (uPos_pos _).ne'
  have hFc := hF.comp (hu.prodMk hσ)
  exact ((Complex.ofRealCLM.contDiff.comp hreal).mul (ex_contDiff.comp haS)).mul
    (invS_contDiff.comp hFc)

lemma bL_hasCompactSupport (δ : ℝ) (F : E m → ℝ → ℂ) :
    HasCompactSupport (fun w : (E (m + 1) × ℝ) × E (m + 1) => bL δ F w.1.1 w.2 w.1.2) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : (E (m + 1) × ℝ) × E (m + 1)) 20)
  intro w hw
  have h0 : cutB m ((w.1.1, w.1.2), w.2) = 0 := by
    apply (cutB m).zero_of_le_dist
    simp only [mem_closedBall, not_le] at hw
    simpa [cutB] using hw.le
  simp [bL, h0]


/-! ## `F` stays near `1` -/

lemma F_near_one (F : E m → ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F))
    (hF0 : ∀ a : E m, ‖a‖ ≤ 12 → F a 0 = 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : E m, ∀ σ : ℝ, ‖a‖ ≤ 12 → |σ| < ε → ‖F a σ - 1‖ < 1 / 2 := by
  have hc : Continuous (Function.uncurry F) := hF.continuous
  have hK : IsCompact (closedBall (0 : E m) 12 ×ˢ ({0} : Set ℝ)) :=
    (isCompact_closedBall _ _).prod isCompact_singleton
  have hO : IsOpen {z : E m × ℝ | ‖Function.uncurry F z - 1‖ < 1 / 2} :=
    isOpen_lt (hc.sub continuous_const).norm continuous_const
  obtain ⟨ε, hε, hsub⟩ := hK.exists_thickening_subset_open hO (by
    rintro ⟨a, s⟩ ⟨ha, hs⟩
    simp only [mem_singleton_iff] at hs
    subst hs
    simp only [mem_closedBall, dist_zero_right] at ha
    simp [hF0 a ha])
  refine ⟨ε, hε, fun a σ ha hσ => ?_⟩
  have : (a, σ) ∈ thickening ε (closedBall (0 : E m) 12 ×ˢ ({0} : Set ℝ)) := by
    rw [mem_thickening_iff]
    refine ⟨(a, 0), ⟨by simpa using ha, rfl⟩, ?_⟩
    rw [Prod.dist_eq]; simpa [Real.dist_eq] using hσ
  exact hsub this

/-! ## The identity `Mker · b = Lker` on the relevant range of `R` -/

/-- Geometry of the support for `0 < τ ≤ 1/16`. -/
lemma support_geom {X Y : E (m + 1)} (h : psiX m X * thetaY m Y ≠ 0) {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : τ ≤ 1 / 16) :
    3 / 8 ≤ vert (X - τ • Y) ∧ ‖(vert (X - τ • Y))⁻¹ • horiz (X - τ • Y)‖ ≤ 12 ∧
      |τ ^ 2 / vert (X - τ • Y)| < τ ∧ ‖((X, τ), Y)‖ ≤ 10 := by
  obtain ⟨hA, hx1, hx2, hY⟩ := region h
  have hyv := abs_vert_le Y
  have hyh := norm_horiz_le Y
  have hw : 3 / 8 ≤ vert (X - τ • Y) := by
    rw [vert_sub_smul]
    have : τ * vert Y ≤ 1 / 8 := by
      calc τ * vert Y ≤ τ * |vert Y| := mul_le_mul_of_nonneg_left (le_abs_self _) hτ0.le
        _ ≤ 1 / 16 * 2 := mul_le_mul hτ (hyv.trans hY.le) (abs_nonneg _) (by norm_num)
        _ = 1 / 8 := by norm_num
    linarith only [this, hx1]
  have hwp : 0 < vert (X - τ • Y) := lt_of_lt_of_le (by norm_num) hw
  refine ⟨hw, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hwp, horiz_sub_smul,
      inv_mul_le_iff₀ hwp]
    have : ‖horiz X - τ • horiz Y‖ ≤ 4 + 1 / 8 := by
      calc ‖horiz X - τ • horiz Y‖ ≤ ‖horiz X‖ + ‖τ • horiz Y‖ := norm_sub_le _ _
        _ = ‖horiz X‖ + τ * ‖horiz Y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ0]
        _ ≤ 4 + 1 / 16 * 2 :=
            add_le_add hA.le (mul_le_mul hτ (hyh.trans hY.le) (norm_nonneg _) (by norm_num))
        _ = 4 + 1 / 8 := by norm_num
    linarith only [this, hw]
  · rw [abs_of_pos (div_pos (pow_pos hτ0 2) hwp), div_lt_iff₀ hwp, sq]
    exact mul_lt_mul_of_pos_left (by linarith only [hτ, hw]) hτ0
  · have hX := norm_le_horiz_add_vert X
    rw [abs_of_pos (lt_trans (by norm_num) hx1)] at hX
    simp only [Prod.norm_def, Real.norm_eq_abs, abs_of_pos hτ0]
    refine max_le (max_le (by linarith only [hX, hA, hx2]) (by linarith only [hτ]))
      (by linarith only [hY])

lemma Mker_mul_bL (δ : ℝ) (F : E m → ℝ → ℂ) (ε : ℝ)
    (hε : ∀ a : E m, ∀ σ : ℝ, ‖a‖ ≤ 12 → |σ| < ε → ‖F a σ - 1‖ < 1 / 2)
    (R : ℝ) (hR0 : 0 < R) (hR16 : R⁻¹ ≤ 1 / 16) (hRε : R⁻¹ ≤ ε) (X Y : E (m + 1)) :
    Mker m δ F R X Y * bL δ F X Y R⁻¹ = Lker m δ R X Y := by
  by_cases h0 : psiX m X * thetaY m Y = 0
  · simp [Mker, Lker, h0]
  obtain ⟨hw, hu, hσ, hcut⟩ := support_geom h0 (inv_pos.2 hR0) hR16
  obtain ⟨-, hx1, -, -⟩ := region h0
  set w := X - R⁻¹ • Y with hwdef
  have hwp : 0 < vert w := lt_of_lt_of_le (by norm_num) hw
  have hPx : uPos (vert X) = vert X := uPos_of_ge (by linarith only [hx1])
  have hPw : uPos (vert w) = vert w := uPos_of_ge (by linarith only [hw])
  have hc1 : cutB m ((X, R⁻¹), Y) = 1 :=
    (cutB m).one_of_mem_closedBall (mem_closedBall_zero_iff.2 hcut)
  set Fv := F (uP w) (R⁻¹ ^ 2 / vert w) with hFv
  have hFn : ‖Fv - 1‖ < 1 / 2 := hε _ _ hu (lt_of_lt_of_le hσ hRε)
  have hF2 : 1 / 2 ≤ ‖Fv‖ := by
    have := norm_sub_norm_le (1 : ℂ) Fv
    rw [norm_one, norm_sub_rev] at this; linarith only [this, hFn]
  have hF0 : Fv ≠ 0 := by intro h; rw [h, norm_zero] at hF2; norm_num at hF2
  have hinv : invS (F ((uPos (vert w))⁻¹ • horiz w) (R⁻¹ ^ 2 / uPos (vert w))) = Fv⁻¹ := by
    rw [hPw]; exact invS_eq hF2
  have hph := phase_id R hR0.ne' X Y (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hx1).ne' hwp.ne'
  rw [← hwdef] at hph
  have hex : ex (-(R ^ 2 * phiP X + R * ⟪graphPt (-uP X), Y⟫)) =
      ex (-(R ^ 2 * phiP w)) * ex (aS X Y R⁻¹) := by
    rw [← ex_add]; congr 1
    rw [aS, hPx, ← hwdef, hPw, hph]; ring
  have hγ : vert w ^ (-gam m δ) * vert w ^ gam m δ = 1 := by
    rw [Real.rpow_neg hwp.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hwp _).ne']
  rw [Lker, hex]
  unfold Mker bL
  rw [← hwdef, hinv, hc1, hPx, hPw, ← hFv]
  have hγc : ((vert w ^ (-gam m δ) : ℝ) : ℂ) * ((vert w ^ gam m δ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hγ, Complex.ofReal_one]
  have hFF : Fv * Fv⁻¹ = 1 := mul_inv_cancel₀ hF0
  push_cast
  linear_combination (↑(psiX m X) * ↑(thetaY m Y) * ↑(vert X ^ (-gam m δ)) *
    ex (-(R ^ 2 * phiP w)) * ex (aS X Y R⁻¹) * ((vert w ^ (-gam m δ) : ℝ) : ℂ) *
      ((vert w ^ gam m δ : ℝ) : ℂ)) * hFF +
    (↑(psiX m X) * ↑(thetaY m Y) * ↑(vert X ^ (-gam m δ)) *
    ex (-(R ^ 2 * phiP w)) * ex (aS X Y R⁻¹)) * hγc


/-! ## Bounds and measurability -/

lemma norm_Mker_le (δ : ℝ) (hδ : 0 < δ) (F : E m → ℝ → ℂ) (ε : ℝ)
    (hε : ∀ a : E m, ∀ σ : ℝ, ‖a‖ ≤ 12 → |σ| < ε → ‖F a σ - 1‖ < 1 / 2)
    (R : ℝ) (hR0 : 0 < R) (hR16 : R⁻¹ ≤ 1 / 16) (hRε : R⁻¹ ≤ ε) (X Y : E (m + 1)) :
    ‖Mker m δ F R X Y‖ ≤ ((3 / 8 : ℝ) ^ gam m δ)⁻¹ * (3 / 2) ∧
      (Mker m δ F R X Y ≠ 0 → (X, Y) ∈ closedBall (0 : E (m + 1)) 7 ×ˢ closedBall 0 2) := by
  have hγ : 0 < gam m δ := by unfold gam; positivity
  by_cases h0 : psiX m X * thetaY m Y = 0
  · have : Mker m δ F R X Y = 0 := by simp [Mker, h0]
    rw [this, norm_zero]
    exact ⟨by positivity, fun h => absurd rfl h⟩
  obtain ⟨hw, hu, hσ, -⟩ := support_geom h0 (inv_pos.2 hR0) hR16
  obtain ⟨hA, hx1, hx2, hY⟩ := region h0
  refine ⟨?_, fun _ => ?_⟩
  · set w := X - R⁻¹ • Y
    have hwp : 0 < vert w := lt_of_lt_of_le (by norm_num) hw
    have hFn : ‖F (uP w) (R⁻¹ ^ 2 / vert w) - 1‖ < 1 / 2 := hε _ _ hu (lt_of_lt_of_le hσ hRε)
    have hF32 : ‖F (uP w) (R⁻¹ ^ 2 / vert w)‖ ≤ 3 / 2 := by
      have := norm_le_norm_sub_add (F (uP w) (R⁻¹ ^ 2 / vert w)) 1
      rw [norm_one] at this; linarith only [this, hFn]
    have hrp : vert w ^ (-gam m δ) ≤ ((3 / 8 : ℝ) ^ gam m δ)⁻¹ := by
      rw [Real.rpow_neg hwp.le]
      exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hw hγ.le)
    have hψθ : |psiX m X * thetaY m Y| ≤ 1 := by
      rw [abs_mul]; exact mul_le_one₀ (abs_psiX_le X) (abs_nonneg _) (abs_thetaY_le Y)
    unfold Mker
    rw [norm_mul, norm_mul, norm_ex, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hwp _)]
    calc |psiX m X * thetaY m Y| * vert w ^ (-gam m δ) * ‖F (uP w) (R⁻¹ ^ 2 / vert w)‖
        ≤ 1 * ((3 / 8 : ℝ) ^ gam m δ)⁻¹ * (3 / 2) :=
          mul_le_mul (mul_le_mul hψθ hrp (Real.rpow_nonneg hwp.le _) zero_le_one) hF32
            (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hX := norm_le_horiz_add_vert X
    rw [abs_of_pos (lt_trans (by norm_num) hx1)] at hX
    simp only [mem_prod, mem_closedBall, dist_zero_right]
    exact ⟨by linarith only [hX, hA, hx2], hY.le⟩

alias Mker_measurable := TaoBR.PBR.PartM.Mker_measurable

lemma bL_bounded (δ : ℝ) (F : E m → ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F)) :
    ∃ B : ℝ, ∀ X Y τ, ‖bL δ F X Y τ‖ ≤ B := by
  obtain ⟨B, hB⟩ := (bL_contDiff δ F hF).continuous.bounded_above_of_compact_support
    (bL_hasCompactSupport δ F)
  exact ⟨B, fun X Y τ => hB ((X, τ), Y)⟩

lemma bL_der_bound (δ : ℝ) (F : E m → ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F))
    (k : ℕ) : ∃ D : ℝ, ∀ y : E (m + 1), ∀ z : E (m + 1) × ℝ,
      ‖iteratedFDeriv ℝ k (fun z : E (m + 1) × ℝ => bL δ F z.1 y z.2) z‖ ≤ D := by
  have hΦ := bL_contDiff δ F hF
  have hcont : Continuous (iteratedFDeriv ℝ k
      (fun w : (E (m + 1) × ℝ) × E (m + 1) => bL δ F w.1.1 w.2 w.1.2)) :=
    hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨D, hD⟩ := hcont.bounded_above_of_compact_support
    ((bL_hasCompactSupport δ F).iteratedFDeriv k)
  refine ⟨D, fun y z => ?_⟩
  set c : (E (m + 1) × ℝ) × E (m + 1) := (0, y)
  have hcomp : (fun z : E (m + 1) × ℝ => bL δ F z.1 y z.2) =
      (fun w : (E (m + 1) × ℝ) × E (m + 1) => bL δ F (w + c).1.1 (w + c).2 (w + c).1.2) ∘
        (ContinuousLinearMap.inl ℝ (E (m + 1) × ℝ) (E (m + 1))) := by
    funext z; simp [c]
  have hΦc : ContDiff ℝ (⊤ : ℕ∞)
      (fun w : (E (m + 1) × ℝ) × E (m + 1) => bL δ F (w + c).1.1 (w + c).2 (w + c).1.2) :=
    hΦ.comp (contDiff_id.add contDiff_const)
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ hΦc _ (by exact_mod_cast le_top)]
  have hshift := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun w : (E (m + 1) × ℝ) × E (m + 1) =>
      bL δ F w.1.1 w.2 w.1.2) k c ((ContinuousLinearMap.inl ℝ (E (m + 1) × ℝ) (E (m + 1))) z)
  rw [hshift]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin k, ‖ContinuousLinearMap.inl ℝ (E (m + 1) × ℝ) (E (m + 1))‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _)
      (fun _ _ => ContinuousLinearMap.norm_inl_le_one _ _ _)
  calc _ ≤ ‖iteratedFDeriv ℝ k (fun w : (E (m + 1) × ℝ) × E (m + 1) => bL δ F w.1.1 w.2 w.1.2)
        ((ContinuousLinearMap.inl ℝ (E (m + 1) × ℝ) (E (m + 1))) z + c)‖ * 1 :=
          mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ ≤ D := by rw [mul_one]; exact hD _

/-! ## Lemma 2.1 applied -/

/-- **L (Lemma 2.1: linearizing the phase).** Restated verbatim from the Blueprint. -/
theorem opNorm_L_le (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (F : E m → ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F))
    (hF0 : ∀ a : E m, ‖a‖ ≤ 12 → F a 0 = 1) (k : ℝ) (hk : 0 < k) :
    ∃ C R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      opNorm p p (kernelOp (Lker m δ R)) ≤
        ENNReal.ofReal C * opNorm p p (kernelOp (Mker m δ F R)) + ENNReal.ofReal (C * R ^ (-k)) := by
  obtain ⟨ε, hε0, hε⟩ := F_near_one F hF hF0
  set τ₀ : ℝ := min (1 / 16) ε with hτ₀def
  have hτ₀ : 0 < τ₀ := lt_min (by norm_num) hε0
  set R₁ : ℝ := τ₀⁻¹ with hR₁def
  have hR₁ : ∀ R : ℝ, R₁ ≤ R → 0 < R ∧ R⁻¹ ≤ 1 / 16 ∧ R⁻¹ ≤ ε := by
    intro R hR
    have hR0 : 0 < R := lt_of_lt_of_le (inv_pos.2 hτ₀) hR
    have : R⁻¹ ≤ τ₀ := by
      have := inv_anti₀ (inv_pos.2 hτ₀) hR
      rwa [inv_inv] at this
    exact ⟨hR0, this.trans (min_le_left _ _), this.trans (min_le_right _ _)⟩
  set Mb : ℝ := ((3 / 8 : ℝ) ^ gam m δ)⁻¹ * (3 / 2) with hMb
  have hMb0 : 0 ≤ Mb := by positivity
  let K : ℝ → E (m + 1) → E (m + 1) → ℂ := fun R => if R₁ ≤ R then Mker m δ F R else 0
  have hKm : ∀ R, Measurable (Function.uncurry (K R)) := by
    intro R
    by_cases h : R₁ ≤ R
    · simp only [K, if_pos h]; exact Mker_measurable δ F hF.continuous R
    · simp only [K, if_neg h]; exact measurable_const
  have hK : ∀ R x y, ‖K R x y‖ ≤ Mb ∧
      (K R x y ≠ 0 → (x, y) ∈ closedBall (0 : E (m + 1)) 7 ×ˢ closedBall 0 2) := by
    intro R x y
    by_cases h : R₁ ≤ R
    · simp only [K, if_pos h]
      obtain ⟨hR0, h16, hRε⟩ := hR₁ R h
      exact norm_Mker_le δ hδ F ε hε R hR0 h16 hRε x y
    · simp only [K, if_neg h, Pi.zero_apply, norm_zero]
      exact ⟨hMb0, fun h' => absurd rfl h'⟩
  obtain ⟨B, hB⟩ := bL_bounded δ F hF
  have hbm : ∀ τ, Measurable (Function.uncurry fun x y => bL δ F x y τ) := by
    intro τ
    have h := (bL_contDiff δ F hF).continuous.comp
      (show Continuous (fun z : E (m + 1) × E (m + 1) => ((z.1, τ), z.2)) by fun_prop)
    exact h.measurable
  have hL := opNorm_le_of_contDiff (m + 1) p p hp hp K
    (closedBall (0 : E (m + 1)) 7 ×ˢ closedBall 0 2)
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)) Mb hKm hK (bL δ F) hbm B hB
    τ₀ hτ₀ univ isOpen_univ (subset_univ _)
    (fun y _ => by
      have hi : ContDiff ℝ (⊤ : ℕ∞)
          (fun z : E (m + 1) × ℝ => ((z, y) : (E (m + 1) × ℝ) × E (m + 1))) :=
        contDiff_id.prodMk contDiff_const
      exact (ContDiff.comp (g := fun w : (E (m + 1) × ℝ) × E (m + 1) => bL δ F w.1.1 w.2 w.1.2)
        (bL_contDiff δ F hF) hi).contDiffOn)
    (fun j => by
      obtain ⟨D, hD⟩ := bL_der_bound δ F hF j
      exact ⟨D, fun y _ z _ => by rw [iteratedFDerivWithin_univ]; exact hD y z⟩)
  obtain ⟨C, R₀, hCR⟩ := hL k hk
  refine ⟨C, max R₀ R₁, fun R hR => ?_⟩
  have h1 := hCR R (le_trans (le_max_left _ _) hR)
  have hRR : R₁ ≤ R := le_trans (le_max_right _ _) hR
  have hKR : K R = Mker m δ F R := if_pos hRR
  obtain ⟨hR0, h16, hRε⟩ := hR₁ R hRR
  have hker : (fun x y => K R x y * bL δ F x y R⁻¹) = Lker m δ R := by
    funext x y; rw [hKR]; exact Mker_mul_bL δ F ε hε R hR0 h16 hRε x y
  rw [hker, hKR] at h1
  exact h1


end PartL

end TaoBR.PBR

end S_PBRPartL

namespace TaoBR.PBR
alias opNorm_L_le := TaoBR.PBR.PartL.opNorm_L_le
end TaoBR.PBR

section S_PBRPartV

/-! # Part V: `localPar_of_opNorm_L` (evaluation on `f(R ·)` and slicing) -/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace

namespace TaoBR.PBR

open Parab

namespace PartV

variable {m : ℕ}

/-! ## Coordinates (copied from `proofs/pbr/PartK.lean`) -/

@[simp] theorem mkPoint_castSucc (u : E m) (t : ℝ) (i : Fin m) :
    mkPoint u t (Fin.castSucc i) = u i := by
  simp [mkPoint]

@[simp] theorem mkPoint_last (u : E m) (t : ℝ) : mkPoint u t (Fin.last m) = t := by
  simp [mkPoint]

@[simp] theorem horiz_mkPoint (u : E m) (t : ℝ) : horiz (mkPoint u t) = u := by
  ext i; simp

@[simp] theorem vert_mkPoint (u : E m) (t : ℝ) : vert (mkPoint u t) = t := by
  simp [vert]

theorem continuous_mkPoint : Continuous fun q : E m × ℝ => mkPoint q.1 q.2 := by
  unfold mkPoint
  apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp
  apply continuous_pi; intro i
  induction i using Fin.lastCases with
  | last => simp; fun_prop
  | cast j => simp; fun_prop

theorem measurable_mkPoint : Measurable fun q : E m × ℝ => mkPoint q.1 q.2 :=
  continuous_mkPoint.measurable

alias measurePreserving_mkPoint := TaoBR.PBR.PartK.measurePreserving_mkPoint

theorem lintegral_mkPoint (m : ℕ) (F : E (m + 1) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ u, ∫⁻ h, F (mkPoint u h) := by
  rw [← (measurePreserving_mkPoint m).lintegral_comp hF]
  exact lintegral_prod _ (hF.comp measurable_mkPoint).aemeasurable

theorem continuous_graphPt : Continuous (fun v : E m => graphPt v) := by
  unfold graphPt
  exact continuous_mkPoint.comp (continuous_id.prodMk (by fun_prop))

theorem measurable_vert : Measurable (fun X : E (m + 1) => vert X) :=
  vert_contDiff.continuous.measurable

theorem measurable_horiz : Measurable (fun X : E (m + 1) => horiz X) :=
  horiz_contDiff.continuous.measurable

theorem measurable_uP : Measurable (fun X : E (m + 1) => uP X) := by
  unfold uP
  exact (measurable_inv.comp measurable_vert).smul measurable_horiz

/-! ## `ex` and cutoffs -/

alias ex_add := TaoBR.PBR.PartL.ex_add

alias norm_ex := TaoBR.PBR.PartM.norm_ex

lemma thetaY_eq_one {Y : E (m + 1)} (h : ‖Y‖ ≤ 1) : thetaY m Y = 1 := by
  unfold thetaY
  exact (thY m).one_of_mem_closedBall (by simpa [thY] using h)

/-- The slab `{1 ≤ Xₙ ≤ 2, |X̲| ≤ (3/2) Xₙ}`. -/
def slab (m : ℕ) : Set (E (m + 1)) :=
  {X | 1 ≤ vert X ∧ vert X ≤ 2 ∧ ‖horiz X‖ ≤ 3 / 2 * vert X}

lemma measurableSet_slab : MeasurableSet (slab m) := by
  unfold slab
  refine (measurableSet_le measurable_const measurable_vert).inter
    ((measurableSet_le measurable_vert measurable_const).inter
      (measurableSet_le measurable_horiz.norm (measurable_vert.const_mul _)))

lemma psiX_eq_one {X : E (m + 1)} (h : X ∈ slab m) : psiX m X = 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold psiX
  rw [betaB.one_of_mem_closedBall, (gamB m).one_of_mem_closedBall, mul_one]
  · simp [gamB]; linarith
  · simp only [betaB, mem_closedBall, Real.dist_eq]
    rw [abs_le]; constructor <;> linarith

/-- The lower bound for `Xₙ^{-γ}` on `[1, 2]`. -/
lemma rpow_lower {t : ℝ} (g : ℝ) (h1 : 1 ≤ t) (h2 : t ≤ 2) : (2 : ℝ) ^ (-|g|) ≤ t ^ (-g) := by
  rcases le_total 0 g with hg | hg
  · rw [abs_of_nonneg hg]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) h2 (by linarith)
  · calc (2 : ℝ) ^ (-|g|) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
          (by linarith [abs_nonneg g])
      _ ≤ t ^ (-g) := Real.one_le_rpow h1 (by linarith)

/-! ## Step 1: evaluation on `f(R ·)` -/

lemma norm_kernelOp_L (δ R : ℝ) (hR : 0 < R) (f : 𝓢(E (m + 1), ℂ))
    (hf : tsupport f ⊆ closedBall 0 R) (X : E (m + 1)) :
    ‖kernelOp (Lker m δ R) (fun y => f (R • y)) X‖ =
      |psiX m X * vert X ^ (-gam m δ)| * (R ^ (m + 1))⁻¹ *
        ‖𝓕 (f : E (m + 1) → ℂ) (graphPt (-uP X))‖ := by
  set w : E (m + 1) := graphPt (-uP X) with hw
  have hθ : ∀ y : E (m + 1), (thetaY m y : ℂ) * f (R • y) = f (R • y) := by
    intro y
    by_cases hf0 : f (R • y) = 0
    · simp [hf0]
    have hm : R • y ∈ closedBall (0 : E (m + 1)) R := hf (subset_tsupport _ hf0)
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR] at hm
    have : ‖y‖ ≤ 1 := le_of_mul_le_mul_left (hm.trans (mul_one R).symm.le) hR
    rw [thetaY_eq_one this]; simp
  set c : ℂ := ((psiX m X * vert X ^ (-gam m δ) : ℝ) : ℂ) * ex (-(R ^ 2 * phiP X))
  have hint : ∀ y : E (m + 1), Lker m δ R X y * f (R • y) = c *
      (Complex.exp (((-2 * Real.pi * ⟪R • y, w⟫ : ℝ) : ℂ) * Complex.I) • f (R • y)) := by
    intro y
    have hex : ex (-(R ^ 2 * phiP X + R * ⟪w, y⟫)) = ex (-(R ^ 2 * phiP X)) *
        Complex.exp (((-2 * Real.pi * ⟪R • y, w⟫ : ℝ) : ℂ) * Complex.I) := by
      rw [show -(R ^ 2 * phiP X + R * ⟪w, y⟫) = -(R ^ 2 * phiP X) + -(R * ⟪w, y⟫) by ring,
        ex_add, real_inner_smul_left, real_inner_comm]
      congr 1
      unfold ex; congr 1; push_cast; ring
    rw [Lker, ← hw, hex, smul_eq_mul]
    conv_rhs => rw [← hθ y]
    simp only [c]; push_cast; ring
  have hk : kernelOp (Lker m δ R) (fun y => f (R • y)) X =
      c * (|(R ^ Module.finrank ℝ (E (m + 1)))⁻¹| • 𝓕 (f : E (m + 1) → ℂ) w) := by
    simp only [kernelOp]
    rw [funext hint, integral_const_mul]
    congr 1
    rw [Real.fourier_eq']
    exact Measure.integral_comp_smul volume (fun v : E (m + 1) =>
      Complex.exp (((-2 * Real.pi * ⟪v, w⟫ : ℝ) : ℂ) * Complex.I) • f v) R
  rw [hk, norm_mul, norm_smul, finrank_euclideanSpace_fin]
  simp only [c, norm_mul, norm_ex, Complex.norm_real, Real.norm_eq_abs, mul_one]
  simp only [abs_mul, abs_inv, abs_pow, abs_of_pos hR]
  ring

/-! ## Step 2: slicing -/

lemma lintegral_comp_inv_smul (t : ℝ) (ht : 1 ≤ t) (Φ : E m → ℝ≥0∞) :
    ∫⁻ u, Φ u ≤ ∫⁻ u, Φ (t⁻¹ • u) := by
  have ht0 : t⁻¹ ≠ 0 := inv_ne_zero (lt_of_lt_of_le one_pos ht).ne'
  have hmap := Measure.map_addHaar_smul (volume : Measure (E m)) ht0
  have h1 : ∫⁻ x, Φ (t⁻¹ • x) =
      ENNReal.ofReal (|((t⁻¹) ^ Module.finrank ℝ (E m))⁻¹|) * ∫⁻ x, Φ x := by
    rw [← smul_eq_mul, ← lintegral_smul_measure, ← hmap]
    haveI : MeasurableConstSMul ℝ (E m) := ⟨fun c => (continuous_const_smul c).measurable⟩
    exact (lintegral_map_equiv Φ (MeasurableEquiv.smul₀ t⁻¹ ht0)).symm
  rw [h1, finrank_euclideanSpace_fin, inv_pow, inv_inv,
    abs_of_pos (by positivity : (0 : ℝ) < t ^ m)]
  refine le_mul_of_one_le_left bot_le ?_
  rw [ENNReal.one_le_ofReal]; exact one_le_pow₀ ht

lemma slice_lower (G : E m → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ v in closedBall (0 : E m) (3 / 2), G v ≤
      ∫⁻ X, (slab m).indicator (fun X => G (-uP X)) X := by
  set H := (slab m).indicator (fun X => G (-uP X)) with hH
  have hHm : Measurable H :=
    (hG.comp measurable_uP.neg).indicator measurableSet_slab
  set Φ : E m → ℝ≥0∞ := (closedBall (0 : E m) (3 / 2)).indicator (fun w => G (-w)) with hΦ
  have hΦ' : ∫⁻ u, Φ u = ∫⁻ v in closedBall (0 : E m) (3 / 2), G v := by
    rw [← lintegral_indicator measurableSet_closedBall]
    have : Φ = fun w => (closedBall (0 : E m) (3 / 2)).indicator G (-w) := by
      funext w
      simp only [hΦ, Set.indicator, mem_closedBall, dist_zero_right, norm_neg]
    rw [this]
    exact lintegral_neg_eq_self _
  have hpt : ∀ t : ℝ, 1 ≤ t → t ≤ 2 → ∀ u : E m, H (mkPoint u t) = Φ (t⁻¹ • u) := by
    intro t h1 h2 u
    have ht0 : 0 < t := lt_of_lt_of_le one_pos h1
    have hiff : mkPoint u t ∈ slab m ↔ t⁻¹ • u ∈ closedBall (0 : E m) (3 / 2) := by
      simp only [slab, Set.mem_setOf_eq, vert_mkPoint, horiz_mkPoint, mem_closedBall,
        dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht0]
      rw [inv_mul_le_iff₀ ht0]
      constructor
      · rintro ⟨-, -, h⟩; linarith only [h]
      · intro h; exact ⟨h1, h2, by linarith only [h]⟩
    have huP : uP (mkPoint u t) = t⁻¹ • u := by simp [uP]
    by_cases hm : mkPoint u t ∈ slab m
    · rw [hH, hΦ, Set.indicator_of_mem hm, Set.indicator_of_mem (hiff.1 hm), huP]
    · rw [hH, hΦ, Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (hiff.2 h))]
  rw [lintegral_mkPoint m H hHm, lintegral_lintegral_swap
    (f := fun u t => H (mkPoint u t)) (hHm.comp measurable_mkPoint).aemeasurable]
  calc ∫⁻ v in closedBall (0 : E m) (3 / 2), G v
      = ∫⁻ t in Set.Icc (1 : ℝ) 2, ∫⁻ v in closedBall (0 : E m) (3 / 2), G v := by
        rw [setLIntegral_const, Real.volume_Icc]; norm_num
    _ ≤ ∫⁻ t in Set.Icc (1 : ℝ) 2, ∫⁻ u, H (mkPoint u t) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        rw [← hΦ', lintegral_congr fun u => hpt t ht.1 ht.2 u]
        exact lintegral_comp_inv_smul t ht.1 Φ
    _ ≤ ∫⁻ t, ∫⁻ u, H (mkPoint u t) := setLIntegral_le_lintegral _ _

/-! ## Step 3: norms and bookkeeping -/

alias eLpNorm_comp_smul := TaoBR.PBR.PartT.eLpNorm_comp_smul

alias eLpNorm_le_opNorm := TaoBR.PBR.PartM.eLpNorm_le_opNorm

lemma lintegral_eq_eLpNorm_rpow {n : ℕ} {p : ℝ} (hp : 1 ≤ p) (u : E n → ℂ) :
    ∫⁻ x, ‖u x‖ₑ ^ p = eLpNorm u (ENNReal.ofReal p) volume ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith), ← ENNReal.rpow_mul, one_div_mul_cancel (by linarith),
    ENNReal.rpow_one]

/-- The estimate at a single scale `R ≥ 1` where the operator bound holds. -/
lemma main_bound (δ : ℝ) {p : ℝ} (hp : 1 ≤ p) (β : ℝ) (D : ℝ≥0) (R : ℝ) (hR : 1 ≤ R)
    (hop : opNorm (ENNReal.ofReal p) (ENNReal.ofReal p) (kernelOp (Lker m δ R)) ≤
      D * ENNReal.ofReal (R ^ β))
    (f : 𝓢(E (m + 1), ℂ)) (hf : tsupport f ⊆ closedBall 0 R) :
    ∫⁻ v in closedBall (0 : E m) (3 / 2), ‖𝓕 (f : E (m + 1) → ℂ) (graphPt v)‖ₑ ^ p ≤
      (ENNReal.ofReal ((2 : ℝ) ^ |gam m δ|) * D) ^ p *
        ENNReal.ofReal (R ^ (β + ((m : ℝ) + 1) - ((m : ℝ) + 1) / p)) ^ p *
          ∫⁻ y, ‖f y‖ₑ ^ p := by
  have hR0 : 0 < R := by linarith
  have hp0' : 0 ≤ p := by linarith
  set P := ENNReal.ofReal p with hPdef
  have hP0 : P ≠ 0 := by simp [hPdef]; linarith
  have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hPr : P.toReal = p := ENNReal.toReal_ofReal hp0'
  set g : E (m + 1) → ℂ := fun y => f (R • y) with hg
  have hmem : MemLp g P volume := by
    refine ⟨(f.continuous.comp (continuous_const_smul R)).aestronglyMeasurable, ?_⟩
    rw [hg, eLpNorm_comp_smul P hP0 hPt _ R hR0]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp P volume).eLpNorm_lt_top
  have key2 := eLpNorm_le_opNorm hop
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hmem
  rw [hg, eLpNorm_comp_smul P hP0 hPt _ R hR0, hPr] at key2
  -- the lower bound
  set G : E m → ℝ≥0∞ := fun v => ‖𝓕 (f : E (m + 1) → ℂ) (graphPt v)‖ₑ ^ p with hGdef
  have hcont : Continuous (𝓕 (f : E (m + 1) → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 f).continuous
  have hGm : Measurable G :=
    ((hcont.comp continuous_graphPt).enorm.measurable).pow_const _
  set c : ℝ := ((2 : ℝ) ^ |gam m δ|)⁻¹ * (R ^ (m + 1))⁻¹ with hc
  have hc0 : 0 < c := by positivity
  have hpt : ∀ X : E (m + 1), ENNReal.ofReal c ^ p *
      (slab m).indicator (fun X => G (-uP X)) X ≤ ‖kernelOp (Lker m δ R) g X‖ₑ ^ p := by
    intro X
    by_cases hX : X ∈ slab m
    · rw [Set.indicator_of_mem hX, hGdef]
      simp only
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0', ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
        ← ENNReal.ofReal_mul hc0.le, hg, norm_kernelOp_L δ R hR0 f hf X]
      refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hp0'
      have hv := rpow_lower (gam m δ) hX.1 hX.2.1
      rw [Real.rpow_neg (by norm_num)] at hv
      rw [psiX_eq_one hX, one_mul, abs_of_pos (lt_of_lt_of_le (by positivity) hv), hc]
      gcongr
    · rw [Set.indicator_of_notMem hX, mul_zero]; exact bot_le
  have hlow : ENNReal.ofReal c ^ p * ∫⁻ v in closedBall (0 : E m) (3 / 2), G v ≤
      ∫⁻ X, ‖kernelOp (Lker m δ R) g X‖ₑ ^ p := by
    calc ENNReal.ofReal c ^ p * ∫⁻ v in closedBall (0 : E m) (3 / 2), G v
        ≤ ENNReal.ofReal c ^ p * ∫⁻ X, (slab m).indicator (fun X => G (-uP X)) X := by
          gcongr; exact slice_lower G hGm
      _ = ∫⁻ X, ENNReal.ofReal c ^ p * (slab m).indicator (fun X => G (-uP X)) X := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0' ENNReal.ofReal_ne_top)]
      _ ≤ _ := lintegral_mono hpt
  rw [lintegral_eq_eLpNorm_rpow hp] at hlow
  rw [lintegral_eq_eLpNorm_rpow hp]
  have hup := ENNReal.rpow_le_rpow key2 hp0'
  set Q : ℝ≥0∞ := (D : ℝ≥0∞) * ENNReal.ofReal (R ^ β) *
    ENNReal.ofReal (R ^ (-((((m + 1 : ℕ) : ℝ)) / p))) with hQ
  have hup' : eLpNorm (kernelOp (Lker m δ R) g) P volume ^ p ≤
      Q ^ p * eLpNorm (f : E (m + 1) → ℂ) P volume ^ p := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0']
    refine hup.trans (le_of_eq ?_)
    rw [hQ]; ring_nf
  have hinv : ENNReal.ofReal c⁻¹ ^ p * ENNReal.ofReal c ^ p = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0', ← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ hc0.ne', ENNReal.ofReal_one, ENNReal.one_rpow]
  have hreal : c⁻¹ * R ^ β * R ^ (-((((m + 1 : ℕ) : ℝ)) / p)) =
      (2 : ℝ) ^ |gam m δ| * R ^ (β + ((m : ℝ) + 1) - ((m : ℝ) + 1) / p) := by
    rw [hc, mul_inv, inv_inv, inv_inv, ← Real.rpow_natCast, mul_assoc, mul_assoc,
      ← Real.rpow_add hR0, ← Real.rpow_add hR0]
    push_cast
    congr 2; ring
  calc ∫⁻ v in closedBall (0 : E m) (3 / 2), G v
      = ENNReal.ofReal c⁻¹ ^ p * (ENNReal.ofReal c ^ p *
          ∫⁻ v in closedBall (0 : E m) (3 / 2), G v) := by rw [← mul_assoc, hinv, one_mul]
    _ ≤ ENNReal.ofReal c⁻¹ ^ p * (Q ^ p * eLpNorm (f : E (m + 1) → ℂ) P volume ^ p) := by
        exact mul_le_mul_right (hlow.trans hup') _
    _ = (D * ENNReal.ofReal (c⁻¹ * R ^ β * R ^ (-((((m + 1 : ℕ) : ℝ)) / p)))) ^ p *
          eLpNorm (f : E (m + 1) → ℂ) P volume ^ p := by
        rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ hp0', hQ,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        ring_nf
    _ = _ := by
        rw [hreal, ENNReal.ofReal_mul (by positivity), ← mul_assoc,
          ENNReal.mul_rpow_of_nonneg ((D : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ |gam m δ|)) _ hp0',
          mul_comm (D : ℝ≥0∞)]

/-- **V (evaluation and slicing).** -/
theorem localPar_of_opNorm_L (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) {p : ℝ} (hp : 1 ≤ p) (β : ℝ)
    (D : ℝ≥0) (R₁ : ℝ)
    (h : ∀ R : ℝ, R₁ ≤ R →
      opNorm (ENNReal.ofReal p) (ENNReal.ofReal p) (kernelOp (Lker m δ R)) ≤
        D * ENNReal.ofReal (R ^ β)) :
    LocPar m p (β + ((m : ℝ) + 1) - ((m : ℝ) + 1) / p) := by
  set α := β + ((m : ℝ) + 1) - ((m : ℝ) + 1) / p with hα
  have hp0' : 0 ≤ p := zero_le_one.trans hp
  set R₂ := max R₁ 1 with hR₂
  have hR₂1 : 1 ≤ R₂ := le_max_right _ _
  set K : ℝ≥0∞ := (ENNReal.ofReal ((2 : ℝ) ^ |gam m δ|) * D) ^ p *
    ENNReal.ofReal (R₂ ^ |α|) ^ p with hK
  have hKt : K ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hp0' (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.coe_ne_top))
    (ENNReal.rpow_ne_top_of_nonneg hp0' ENNReal.ofReal_ne_top)
  refine ⟨K.toNNReal, fun R hR f hf => ?_⟩
  rw [ENNReal.coe_toNNReal hKt]
  set R' := max R R₂ with hR'
  have hR'1 : 1 ≤ R' := le_trans hR (le_max_left _ _)
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hfR' : tsupport f ⊆ closedBall 0 R' :=
    hf.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hb := main_bound δ hp β D R' hR'1
    (h R' (le_trans (le_max_left _ _) (le_max_right _ _))) f hfR'
  rw [← hα] at hb
  have hRα : R' ^ α ≤ R₂ ^ |α| * R ^ α := by
    have hle : R' ≤ R₂ * R := by
      rcases le_total R R₂ with h' | h'
      · rw [hR', max_eq_right h']; exact le_mul_of_one_le_right (zero_le_one.trans hR₂1) hR
      · rw [hR', max_eq_left h']; exact le_mul_of_one_le_left hR0.le hR₂1
    rcases le_total 0 α with hα0 | hα0
    · rw [abs_of_nonneg hα0, ← Real.mul_rpow (zero_le_one.trans hR₂1) hR0.le]
      exact Real.rpow_le_rpow (zero_le_one.trans hR'1) hle hα0
    · calc R' ^ α ≤ R ^ α := Real.rpow_le_rpow_of_nonpos hR0 (le_max_left _ _) hα0
        _ ≤ R₂ ^ |α| * R ^ α := le_mul_of_one_le_left (by positivity)
            (Real.one_le_rpow hR₂1 (abs_nonneg _))
  refine hb.trans ?_
  rw [hK, mul_assoc _ (ENNReal.ofReal (R₂ ^ |α|) ^ p)]
  gcongr
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0', ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hRα) hp0'

end PartV

end TaoBR.PBR

end S_PBRPartV

namespace TaoBR.PBR
alias localPar_of_opNorm_L := TaoBR.PBR.PartV.localPar_of_opNorm_L
end TaoBR.PBR

section S_PBRPartH

/-! # Part H: `thick_of_localPar` (thickening by modulation) -/

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace

namespace TaoBR.PBR

open Parab

namespace PartH

variable {m : ℕ}

/-! ## Coordinates (copied from `proofs/pbr/PartK.lean`, `proofs/parab/PartF.lean`) -/

export TaoBR.PBR.PartK (mkPoint_castSucc mkPoint_last horiz_mkPoint vert_mkPoint ext_hv mkPoint_horiz_vert inner_mkPoint measurePreserving_mkPoint)






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



/-- The shear `(v, s) ↦ mkPoint v (s + |v|²/2)` is measure preserving. -/
theorem measurePreserving_shear (m : ℕ) :
    MeasurePreserving (fun q : E m × ℝ => mkPoint q.1 (q.2 + ‖q.1‖ ^ 2 / 2))
      (volume.prod volume) volume := by
  have hs : MeasurePreserving (fun q : E m × ℝ => (q.1, q.2 + ‖q.1‖ ^ 2 / 2))
      ((volume : Measure (E m)).prod (volume : Measure ℝ)) (volume.prod volume) := by
    refine (MeasurePreserving.id (volume : Measure (E m))).skew_product
      (g := fun (v : E m) (s : ℝ) => s + ‖v‖ ^ 2 / 2) (by fun_prop) ?_
    exact ae_of_all _ fun v => map_add_right_eq_self _ _
  exact (measurePreserving_mkPoint m).comp hs

theorem inner_mkPoint_right (y : E (m + 1)) (v : E m) (t : ℝ) :
    ⟪y, mkPoint v t⟫ = ⟪horiz y, v⟫ + vert y * t := by
  conv_lhs => rw [← mkPoint_horiz_vert y]
  exact inner_mkPoint _ _ _ _

/-! ## Geometry of the thickening -/

/-- A point within `ρ ≤ 1/16` of the paraboloid piece `parabSet m` has `|η̲| ≤ 3/2` and
`|ηₙ - |η̲|²/2| < 3ρ`. -/
theorem thick_geom {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 16) {η : E (m + 1)}
    (hη : η ∈ thickening ρ (parabSet m)) :
    ‖horiz η‖ ≤ 3 / 2 ∧ |vert η - ‖horiz η‖ ^ 2 / 2| < 3 * ρ := by
  obtain ⟨z, ⟨u, hu, rfl⟩, hd⟩ := mem_thickening_iff.1 hη
  rw [mem_closedBall, dist_zero_right] at hu
  rw [dist_eq_norm] at hd
  have hsub : η - graphPt u = mkPoint (horiz η - u) (vert η - ‖u‖ ^ 2 / 2) := by
    conv_lhs => rw [← mkPoint_horiz_vert η]
    rw [graphPt, mkPoint_sub]
  have hn := norm_mkPoint_sq (horiz η - u) (vert η - ‖u‖ ^ 2 / 2)
  rw [← hsub] at hn
  set d := ‖η - graphPt u‖ with hdd
  set a := ‖horiz η - u‖ with ha
  set b := vert η - ‖u‖ ^ 2 / 2 with hb
  set h := ‖horiz η‖ with hh
  have hd0 : 0 ≤ d := norm_nonneg _
  have ha0 : 0 ≤ a := norm_nonneg _
  have hd2 : d ^ 2 < ρ ^ 2 := pow_lt_pow_left₀ hd hd0 two_ne_zero
  have haρ : a < ρ := lt_of_pow_lt_pow_left₀ 2 hρ.le
    (by linarith only [hn, hd2, sq_nonneg b])
  have hbρ : |b| < ρ := abs_lt_of_sq_lt_sq (by linarith only [hn, hd2, sq_nonneg a]) hρ.le
  have h1 : h ≤ ‖u‖ + a := by
    have := norm_le_norm_add_norm_sub' (horiz η) u
    simpa [hh, ha] using this
  have h2 : ‖u‖ ≤ h + a := by
    have := norm_le_norm_add_norm_sub' u (horiz η)
    rw [norm_sub_rev] at this
    simpa [hh, ha] using this
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hh0 : 0 ≤ h := norm_nonneg _
  refine ⟨by linarith only [h1, hu, haρ, hρ1], ?_⟩
  have hkey : vert η - h ^ 2 / 2 = b + (‖u‖ - h) * (‖u‖ + h) / 2 := by rw [hb]; ring
  rw [hkey]
  obtain ⟨hb1, hb2⟩ := abs_lt.1 hbρ
  have hs : ‖u‖ + h ≤ 11 / 4 := by linarith only [h1, hu, haρ, hρ1]
  have hs0 : 0 ≤ ‖u‖ + h := add_nonneg hu0 hh0
  have e1 : (‖u‖ - h) * (‖u‖ + h) ≤ a * (11 / 4) :=
    (mul_le_mul_of_nonneg_right (show ‖u‖ - h ≤ a by linarith only [h2]) hs0).trans
      (mul_le_mul_of_nonneg_left hs ha0)
  have e2' : (h - ‖u‖) * (‖u‖ + h) ≤ a * (11 / 4) :=
    (mul_le_mul_of_nonneg_right (show h - ‖u‖ ≤ a by linarith only [h1]) hs0).trans
      (mul_le_mul_of_nonneg_left hs ha0)
  have e2 : -(a * (11 / 4)) ≤ (‖u‖ - h) * (‖u‖ + h) := by
    rw [show (‖u‖ - h) * (‖u‖ + h) = -((h - ‖u‖) * (‖u‖ + h)) by ring]
    exact neg_le_neg e2'
  rw [abs_lt]; constructor <;> linarith only [e1, e2, hb1, hb2, haρ, hρ]

/-! ## Modulation -/

theorem contDiff_modChar (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) fun x : E (m + 1) => ((𝐞 (-(s * vert x)) : Circle) : ℂ) := by
  simp only [Real.fourierChar_apply]
  apply Complex.contDiff_exp.comp
  apply ContDiff.mul _ contDiff_const
  exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_const.mul vert_contDiff).neg)

theorem enorm_circle (z : Circle) : ‖(z : ℂ)‖ₑ = 1 := by
  rw [← ofReal_norm, Circle.norm_coe, ENNReal.ofReal_one]

/-- The modulation `f_s = e(-s yₙ) f` translates `f̂` vertically by `s`. -/
theorem exists_modulate (R : ℝ) (f : 𝓢(E (m + 1), ℂ)) (hf : tsupport f ⊆ closedBall 0 R)
    (s : ℝ) :
    ∃ g : 𝓢(E (m + 1), ℂ), tsupport g ⊆ closedBall 0 R ∧
      (∀ v : E m, 𝓕 (g : E (m + 1) → ℂ) (graphPt v) =
        𝓕 (f : E (m + 1) → ℂ) (mkPoint v (s + ‖v‖ ^ 2 / 2))) ∧
      ∀ y, ‖g y‖ₑ = ‖f y‖ₑ := by
  have hfc : HasCompactSupport (f : E (m + 1) → ℂ) :=
    (isCompact_closedBall 0 R).of_isClosed_subset (isClosed_tsupport _) hf
  set F : E (m + 1) → ℂ := fun y => ((𝐞 (-(s * vert y)) : Circle) : ℂ) * f y with hF
  have hc : HasCompactSupport F := hfc.mul_left
  have hcd : ContDiff ℝ (⊤ : ℕ∞) F := (contDiff_modChar s).mul (f.smooth ⊤)
  refine ⟨hc.toSchwartzMap hcd, ?_, fun v => ?_, fun y => ?_⟩
  · change tsupport F ⊆ _
    exact tsupport_mul_subset_right.trans hf
  · change 𝓕 F (graphPt v) = _
    rw [Real.fourier_eq, Real.fourier_eq]
    congr 1; ext y
    simp only [hF, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, graphPt,
      inner_mkPoint_right]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  · change ‖F y‖ₑ = _
    simp only [hF, enorm_mul, enorm_circle, one_mul]

/-! ## The thickened estimate -/

/-- **H.** Verbatim restatement of the Blueprint's `thick_of_localPar`. -/
theorem thick_of_localPar (m : ℕ) (hm : 1 ≤ m) {p : ℝ} (hp : 1 ≤ p) {α : ℝ}
    (h : LocPar m p α) : ThickRestr (parabSet m) p α := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun R hR f hf => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  set ρ : ℝ := 1 / (16 * R) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 / 16 := by
    rw [hρ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [hR]
  set G : E (m + 1) → ℝ≥0∞ := fun η => ‖𝓕 (f : E (m + 1) → ℂ) η‖ₑ ^ p with hG
  have hGm : Measurable G := by
    have hc : Continuous (𝓕 (f : E (m + 1) → ℂ)) := by
      rw [← SchwartzMap.fourier_coe]; exact (𝓕 f).continuous
    exact hc.enorm.measurable.pow_const p
  set S' : Set (E (m + 1)) :=
    {η | ‖horiz η‖ ≤ 3 / 2} ∩ {η | |vert η - ‖horiz η‖ ^ 2 / 2| < 3 * ρ} with hS'
  have hS'm : MeasurableSet S' := by
    have hh : Continuous (fun η : E (m + 1) => horiz η) := horiz_contDiff.continuous
    have hv : Continuous (fun η : E (m + 1) => vert η) := vert_contDiff.continuous
    exact (measurableSet_le (hh.norm.measurable) measurable_const).inter
      (measurableSet_lt ((hv.sub ((hh.norm.pow 2).div_const 2)).abs.measurable) measurable_const)
  have hsub : thickening (1 / (16 * R)) (parabSet m) ⊆ S' := fun η hη =>
    let h := thick_geom hρ0 hρ1 hη; ⟨h.1, h.2⟩
  set I : Set ℝ := Ioo (-(3 * ρ)) (3 * ρ) with hI
  set B : Set (E m) := closedBall (0 : E m) (3 / 2) with hB
  set K : ℝ → ℝ≥0∞ := fun s => ∫⁻ v in B, G (mkPoint v (s + ‖v‖ ^ 2 / 2)) with hKdef
  have hK : ∀ s, K s ≤ C * ENNReal.ofReal (R ^ α) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p := by
    intro s
    obtain ⟨g, hg, hgF, hgn⟩ := exists_modulate R f hf s
    have := hC R hR g hg
    simp only [hgF, hgn] at this
    exact this
  have hpt : ∀ (v : E m) (s : ℝ), S'.indicator G (mkPoint v (s + ‖v‖ ^ 2 / 2)) =
      I.indicator (fun s => B.indicator (fun v => G (mkPoint v (s + ‖v‖ ^ 2 / 2))) v) s := by
    intro v s
    have e : s + ‖v‖ ^ 2 / 2 - ‖v‖ ^ 2 / 2 = s := by ring
    have hmem : mkPoint v (s + ‖v‖ ^ 2 / 2) ∈ S' ↔ v ∈ B ∧ s ∈ I := by
      change (‖horiz (mkPoint v (s + ‖v‖ ^ 2 / 2))‖ ≤ 3 / 2 ∧
        |vert (mkPoint v (s + ‖v‖ ^ 2 / 2)) - ‖horiz (mkPoint v (s + ‖v‖ ^ 2 / 2))‖ ^ 2 / 2| <
          3 * ρ) ↔ _
      rw [vert_mkPoint, horiz_mkPoint, e, hB, hI, mem_closedBall, dist_zero_right, abs_lt]
      rfl
    by_cases h1 : v ∈ B <;> by_cases h2 : s ∈ I
    · rw [Set.indicator_of_mem h2, Set.indicator_of_mem h1, Set.indicator_of_mem (hmem.2 ⟨h1, h2⟩)]
    · rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem (fun h => h2 (hmem.1 h).2)]
    · rw [Set.indicator_of_mem h2, Set.indicator_of_notMem h1,
        Set.indicator_of_notMem (fun h => h1 (hmem.1 h).1)]
    · rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem (fun h => h2 (hmem.1 h).2)]
  have hinner : ∀ s, ∫⁻ v, I.indicator (fun s => B.indicator
      (fun v => G (mkPoint v (s + ‖v‖ ^ 2 / 2))) v) s = I.indicator K s := by
    intro s
    by_cases hs : s ∈ I
    · simp only [Set.indicator_of_mem hs, hKdef]
      exact lintegral_indicator measurableSet_closedBall _
    · simp only [Set.indicator_of_notMem hs, lintegral_zero]
  have hmeas : Measurable fun q : E m × ℝ => S'.indicator G (mkPoint q.1 (q.2 + ‖q.1‖ ^ 2 / 2)) :=
    (hGm.indicator hS'm).comp (measurePreserving_shear m).measurable
  calc ∫⁻ η in thickening (1 / (16 * R)) (parabSet m), ‖𝓕 (f : E (m + 1) → ℂ) η‖ₑ ^ p
      ≤ ∫⁻ η in S', G η := lintegral_mono_set hsub
    _ = ∫⁻ η, S'.indicator G η := (lintegral_indicator hS'm G).symm
    _ = ∫⁻ q : E m × ℝ, S'.indicator G (mkPoint q.1 (q.2 + ‖q.1‖ ^ 2 / 2)) ∂(volume.prod volume) :=
        ((measurePreserving_shear m).lintegral_comp (hGm.indicator hS'm)).symm
    _ = ∫⁻ s, ∫⁻ v, S'.indicator G (mkPoint v (s + ‖v‖ ^ 2 / 2)) :=
        lintegral_prod_symm' _ hmeas
    _ = ∫⁻ s, I.indicator K s := by
        simp only [hpt, hinner]
    _ = ∫⁻ s in I, K s := lintegral_indicator measurableSet_Ioo K
    _ ≤ ∫⁻ _ in I, C * ENNReal.ofReal (R ^ α) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p := lintegral_mono hK
    _ = C * ENNReal.ofReal (R ^ α) ^ p * (∫⁻ y, ‖f y‖ₑ ^ p) * ENNReal.ofReal (6 * ρ) := by
        rw [setLIntegral_const, hI, Real.volume_Ioo]; congr 2; ring
    _ ≤ C * ENNReal.ofReal (R ^ α) ^ p * (∫⁻ y, ‖f y‖ₑ ^ p) * ENNReal.ofReal (1 / R) := by
        refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
        rw [hρ, show 6 * (1 / (16 * R)) = (3 / 8) * (1 / R) by ring]
        have : 0 ≤ 1 / R := one_div_nonneg.2 hR0.le
        linarith only [this]
    _ = C * ENNReal.ofReal (R ^ α) ^ p * ENNReal.ofReal (1 / R) * ∫⁻ y, ‖f y‖ₑ ^ p := by ring

end PartH

end TaoBR.PBR

end S_PBRPartH

namespace TaoBR.PBR
alias thick_of_localPar := TaoBR.PBR.PartH.thick_of_localPar
end TaoBR.PBR

section S_PBRTarget

open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace

namespace TaoBR.PBR

open Parab

/-! ## Assembly -/

/-- PBR ⟹ the thickened parabolic estimate at `p_c` with loss `2δ`, for every `δ > 0`. -/
theorem thick_of_pbr (m : ℕ) (hm : 1 ≤ m) (hPBR : ParabolicBochnerRieszConjecture m) (δ : ℝ)
    (hδ : 0 < δ) : ThickRestr (parabSet m) (pc m) (2 * δ) := by
  set P := ENNReal.ofReal (pc m) with hPdef
  have hpc1 := one_lt_pc m hm
  have hP1 : 1 ≤ P := by rw [hPdef, ENNReal.one_le_ofReal]; exact hpc1.le
  have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hPr : P.toReal = pc m := ENNReal.toReal_ofReal (pc_pos m).le
  have hPBRδ := hPBR (etaP m) etaP_contDiff etaP_hasCompactSupport P hP1 δ
    (by rw [hPdef, critIndex_pc]; exact hδ)
  obtain ⟨C₀, hT⟩ := opNorm_T_le m hm P hP1 hPt δ hδ hPBRδ
  obtain ⟨F, hF, hF0, C₁, R₀, hM⟩ := opNorm_M_le m hm P hP1 hPt δ hδ C₀ hT
  obtain ⟨C₂, R₂, hL⟩ := opNorm_L_le m hm δ hδ P hP1 F hF hF0 ((m : ℝ) / 2 + 1) (by positivity)
  set β := 2 * δ + 1 - ((m : ℝ) + 1) / pc m with hβ
  have hβ' : β = 2 * δ - (m : ℝ) / 2 := by rw [hβ, div_pc]; ring
  have hloc := localPar_of_opNorm_L m hm δ hpc1.le β
    (Real.toNNReal C₂ * C₁ + Real.toNNReal C₂) (max (max R₀ R₂) 1) (fun R hR => by
      have hR0 : R₀ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
      have hR2 : R₂ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
      have hR1 : 1 ≤ R := le_trans (le_max_right _ _) hR
      have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
      have hMR := hM R hR0
      rw [hPr] at hMR
      have hk : R ^ (-((m : ℝ) / 2 + 1)) ≤ R ^ β :=
        Real.rpow_le_rpow_of_exponent_le hR1 (by rw [hβ']; linarith only [hδ])
      calc opNorm P P (kernelOp (Lker m δ R))
          ≤ ENNReal.ofReal C₂ * opNorm P P (kernelOp (Mker m δ F R)) +
              ENNReal.ofReal (C₂ * R ^ (-((m : ℝ) / 2 + 1))) := hL R hR2
        _ ≤ ENNReal.ofReal C₂ * (C₁ * ENNReal.ofReal (R ^ β)) +
              ENNReal.ofReal C₂ * ENNReal.ofReal (R ^ β) := by
            gcongr
            rw [ENNReal.ofReal_mul' (by positivity)]
            gcongr
        _ = ((Real.toNNReal C₂ * C₁ + Real.toNNReal C₂ : ℝ≥0) : ℝ≥0∞) *
              ENNReal.ofReal (R ^ β) := by
            rw [ENNReal.ofReal]; push_cast; ring)
  have hexp : β + ((m : ℝ) + 1) - ((m : ℝ) + 1) / pc m = 2 * δ := by
    rw [hβ, div_pc]; ring
  rw [hexp] at hloc
  exact thick_of_localPar m hm hpc1.le hloc

/-- **Target** (Tao, p. 10), proved from the stubs. -/
theorem target_proof (m : ℕ) (hm : 1 ≤ m) :
    ParabolicRestrictionConjecture m ↔ ParabolicBochnerRieszConjecture m := by
  refine ⟨parabolicBochnerRieszConjecture_of_parabolicRestrictionConjecture m hm,
    fun hPBR => ?_⟩
  obtain ⟨κ, α₀, hα₀, hR⟩ := restrMu_zero_of_thick (by omega : 2 ≤ m + 1) (goodMeasure_parab m hm)
  intro p hp hpc
  have hptop : p ≠ ⊤ := ne_top_of_lt hpc
  set q := p.toReal with hqdef
  have hq1 : 1 ≤ q := by
    have := ENNReal.toReal_mono hptop hp
    simpa using this
  have hqc : q < pc m := (ENNReal.lt_ofReal_iff_toReal_lt hptop).mp hpc
  have hab : 1 / pc m < 1 / q := one_div_lt_one_div_of_lt (by linarith) hqc
  obtain ⟨α, hα, hαα, hkey⟩ := exists_small_alpha κ α₀ (1 / pc m) (1 / q) hα₀ hab
  have hthick : ThickRestr (parabSet m) (pc m) α := by
    have := thick_of_pbr m hm hPBR (α / 2) (by positivity)
    rwa [show 2 * (α / 2) = α by ring] at this
  have hR0 := hR (pc m) (one_lt_pc m hm) (pc_lt_two m) α hα hαα hthick q hq1 hkey
  obtain ⟨C, hC⟩ := parabolic_of_restrMu m hq1 hR0
  refine ⟨C, fun f => ?_⟩
  have := hC f
  rwa [hqdef, ENNReal.ofReal_toReal hptop] at this

end TaoBR.PBR

end S_PBRTarget

theorem solution (m : ℕ) (hm : 1 ≤ m) :
    TaoBR.ParabolicRestrictionConjecture m ↔ TaoBR.ParabolicBochnerRieszConjecture m :=
  TaoBR.PBR.target_proof m hm

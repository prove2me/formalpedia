-- Prove2me | solution 1 for TaoBR.restr_two_mul_of_br
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T02:52:25.529653+00:00
-- url     : https://prove2.me/submissions/e6777dfd-3c0b-4ae2-bfb9-86d03de75669

import Mathlib
import Definitions.Def_TaoBR
import Theorems.Thm_TaoBR_carlesonSjolinOp_le_of_br
import Theorems.Thm_TaoBR_opNorm_le_of_contDiff

/-!
# Tao 1999, Theorem 1.1: `BR(p, α) ⇒ R(p, 2α)` for `1 ≤ p ≤ 2n/(n+1)`

Route (Tao §2): Carleson–Sjölin bound at scale `R²` for `ψ(x,y) = χ(x) η(y)`, rescale
`y = ỹ/R` (kernel `K R`), remove the phase error `a(x, ỹ, 1/R)` with Lemma 2.1 (kernel `K' R`),
evaluate `K' R` on `f(R ·)` as `χ(x) e^{2πiR²|x|} R^{-n} f̂(x/|x|)`, and use polar coordinates.
-/

open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace

namespace TaoBR
namespace RTB

variable {n : ℕ}

/-! ## Cutoffs -/

/-- `= 1` on `closedBall 0 4.8`, supported in `ball 0 5`. -/
noncomputable def bOut (n : ℕ) : ContDiffBump (0 : E n) := ⟨4.8, 5, by norm_num, by norm_num⟩
/-- `= 1` on `closedBall 0 4`, supported in `ball 0 4.2`. -/
noncomputable def bIn (n : ℕ) : ContDiffBump (0 : E n) := ⟨4, 4.2, by norm_num, by norm_num⟩
/-- `= 1` on `closedBall 0 2`, supported in `ball 0 3`. -/
noncomputable def bEta (n : ℕ) : ContDiffBump (0 : E n) := ⟨2, 3, by norm_num, by norm_num⟩
/-- `= 1` on `closedBall 0 1`, supported in `ball 0 2`. -/
noncomputable def bTheta (n : ℕ) : ContDiffBump (0 : E n) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The shell cutoff `χ`, supported in `4 < |x| < 5`, equal to `1` on `4.2 ≤ |x| ≤ 4.8`. -/
noncomputable def chi (n : ℕ) (x : E n) : ℝ := bOut n x - bIn n x
noncomputable def eta (n : ℕ) (y : E n) : ℝ := bEta n y
noncomputable def theta (n : ℕ) (y : E n) : ℝ := bTheta n y

/-- The Carleson–Sjölin amplitude `ψ(x, y) = χ(x) η(y)`. -/
noncomputable def psi (n : ℕ) (x y : E n) : ℝ := chi n x * eta n y

lemma chi_ne_zero {x : E n} (h : chi n x ≠ 0) : 4 < ‖x‖ ∧ ‖x‖ < 5 := by
  by_contra hc
  apply h
  rcases not_and_or.1 hc with h1 | h1
  · push_neg at h1
    have hm : x ∈ closedBall (0 : E n) 4 := by simpa using h1
    have e1 : bOut n x = 1 := (bOut n).one_of_mem_closedBall
      (closedBall_subset_closedBall (by norm_num [bOut]) hm)
    have e2 : bIn n x = 1 := (bIn n).one_of_mem_closedBall hm
    simp [chi, e1, e2]
  · push_neg at h1
    have e1 : bOut n x = 0 := (bOut n).zero_of_le_dist (by simpa [bOut] using h1)
    have e2 : bIn n x = 0 := (bIn n).zero_of_le_dist (by simp [bIn]; linarith)
    simp [chi, e1, e2]
lemma chi_eq_one {x : E n} (h1 : 4.2 ≤ ‖x‖) (h2 : ‖x‖ ≤ 4.8) : chi n x = 1 := by
  have e1 : bOut n x = 1 := (bOut n).one_of_mem_closedBall (by simpa [bOut] using h2)
  have e2 : bIn n x = 0 := (bIn n).zero_of_le_dist (by simpa [bIn] using h1)
  simp [chi, e1, e2]
lemma abs_chi_le (x : E n) : |chi n x| ≤ 1 := by
  have := (bOut n).nonneg' x; have := (bOut n).le_one (x := x)
  have := (bIn n).nonneg' x; have := (bIn n).le_one (x := x)
  rw [abs_le]; constructor <;> simp only [chi] <;> linarith
lemma theta_ne_zero {y : E n} (h : theta n y ≠ 0) : ‖y‖ < 2 := by
  by_contra hc; push_neg at hc
  exact h ((bTheta n).zero_of_le_dist (by simpa [bTheta] using hc))
lemma theta_eq_one {y : E n} (h : ‖y‖ ≤ 1) : theta n y = 1 :=
  (bTheta n).one_of_mem_closedBall (by simpa [bTheta] using h)
lemma abs_theta_le (y : E n) : |theta n y| ≤ 1 := by
  have := (bTheta n).nonneg' y; have := (bTheta n).le_one (x := y)
  rw [abs_le]; constructor <;> simp only [theta] <;> linarith
lemma eta_eq_one {y : E n} (h : ‖y‖ ≤ 2) : eta n y = 1 :=
  (bEta n).one_of_mem_closedBall (by simpa [bEta] using h)
lemma eta_ne_zero {y : E n} (h : eta n y ≠ 0) : ‖y‖ < 3 := by
  by_contra hc; push_neg at hc
  exact h ((bEta n).zero_of_le_dist (by simpa [bEta] using hc))
lemma chi_contDiff : ContDiff ℝ (⊤ : ℕ∞) (chi n) :=
  (bOut n).contDiff.sub (bIn n).contDiff
lemma theta_contDiff : ContDiff ℝ (⊤ : ℕ∞) (theta n) := (bTheta n).contDiff

lemma psi_contDiff : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (psi n)) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : E n × E n => chi n z.1) := chi_contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : E n × E n => eta n z.2) :=
    (bEta n).contDiff.comp contDiff_snd
  exact h1.mul h2
lemma psi_hasCompactSupport : HasCompactSupport (Function.uncurry (psi n)) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : E n) 5 |>.prod (isCompact_closedBall 0 3))
  intro z hz
  by_contra h
  have h' : chi n z.1 * eta n z.2 ≠ 0 := h
  have a := chi_ne_zero (left_ne_zero_of_mul h')
  have b := eta_ne_zero (right_ne_zero_of_mul h')
  exact hz ⟨by simpa using a.2.le, by simpa using b.le⟩
lemma psi_sep : ∃ c : ℝ, 0 < c ∧ ∀ x y, psi n x y ≠ 0 → c ≤ ‖x - y‖ := by
  refine ⟨1, one_pos, fun x y h => ?_⟩
  have a := chi_ne_zero (left_ne_zero_of_mul h)
  have b := eta_ne_zero (right_ne_zero_of_mul h)
  have := norm_sub_norm_le x y
  linarith

/-! ## The kernels -/

/-- The rescaled Carleson–Sjölin kernel `e^{2πiR²|x - ỹ/R|} χ(x) θ(ỹ)`. -/
noncomputable def K (n : ℕ) (R : ℝ) (x y : E n) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (R ^ 2 * ‖x - R⁻¹ • y‖ : ℝ)) * (chi n x * theta n y : ℝ)

/-- The linearized kernel `e^{2πi(R²|x| - R⟨x/|x|, ỹ⟩)} χ(x) θ(ỹ)`. -/
noncomputable def K' (n : ℕ) (R : ℝ) (x y : E n) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (R ^ 2 * ‖x‖ - R * ⟪x, y⟫ / ‖x‖ : ℝ)) *
    (chi n x * theta n y : ℝ)

/-- A globally smooth positive function equal to `t` for `t ≥ 1/4`. -/
noncomputable def uPos (t : ℝ) : ℝ := 1 / 8 + (t - 1 / 8) * Real.smoothTransition (8 * t - 1)

/-- A globally smooth function equal to `√t` for `t ≥ 1/4`. -/
noncomputable def sq (t : ℝ) : ℝ := Real.sqrt (uPos t)

/-- The phase error `a(x, ỹ, τ)` with `|x - τỹ|/τ² = |x|/τ² - ⟨x/|x|, ỹ⟩/τ + a` on the support. -/
noncomputable def phaseErr (x y : E n) (τ : ℝ) : ℝ :=
  sq (‖x‖ ^ 2) * (‖y‖ ^ 2 / (2 * sq (‖x‖ ^ 2) ^ 2) -
    ((-2 * ⟪x, y⟫ + τ * ‖y‖ ^ 2) / sq (‖x‖ ^ 2) ^ 2) ^ 2 /
      (2 * (1 + sq (1 + τ * ((-2 * ⟪x, y⟫ + τ * ‖y‖ ^ 2) / sq (‖x‖ ^ 2) ^ 2))) ^ 2))

/-- The Lemma 2.1 multiplier `b = e^{-2πi a}`. -/
noncomputable def bfun (x y : E n) (τ : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * (phaseErr x y τ : ℝ)))

/-! ## Smoothness of the phase error -/

lemma uPos_of_ge {t : ℝ} (h : 1 / 4 ≤ t) : uPos t = t := by
  rw [uPos, Real.smoothTransition.one_of_one_le (by linarith)]; ring

lemma uPos_pos (t : ℝ) : 0 < uPos t := by
  unfold uPos
  rcases le_or_gt (1 / 8) t with h | h
  · have := Real.smoothTransition.nonneg (8 * t - 1)
    nlinarith
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; norm_num

lemma sq_of_ge {t : ℝ} (h : 1 / 4 ≤ t) : sq t = Real.sqrt t := by rw [sq, uPos_of_ge h]

lemma sq_pos (t : ℝ) : 0 < sq t := Real.sqrt_pos.2 (uPos_pos t)

lemma uPos_contDiff : ContDiff ℝ (⊤ : ℕ∞) uPos := by
  unfold uPos
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)))

lemma sq_contDiff : ContDiff ℝ (⊤ : ℕ∞) sq :=
  uPos_contDiff.sqrt fun t => (uPos_pos t).ne'

lemma phaseErr_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (fun w : (E n × ℝ) × E n => phaseErr w.1.1 w.2 w.1.2) := by
  have hX : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E n × ℝ) × E n => w.1.1) := contDiff_fst.comp contDiff_fst
  have hT : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E n × ℝ) × E n => w.1.2) := contDiff_snd.comp contDiff_fst
  have hY : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E n × ℝ) × E n => w.2) := contDiff_snd
  have hr : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E n × ℝ) × E n => sq (‖w.1.1‖ ^ 2)) :=
    sq_contDiff.comp ((contDiff_norm_sq ℝ).comp hX)
  have hr0 : ∀ w : (E n × ℝ) × E n, sq (‖w.1.1‖ ^ 2) ^ 2 ≠ 0 :=
    fun w => pow_ne_zero 2 (sq_pos _).ne'
  have hP : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E n × ℝ) × E n => ⟪w.1.1, w.2⟫) := hX.inner ℝ hY
  have hQ : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E n × ℝ) × E n => ‖w.2‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp hY
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E n × ℝ) × E n =>
      (-2 * ⟪w.1.1, w.2⟫ + w.1.2 * ‖w.2‖ ^ 2) / sq (‖w.1.1‖ ^ 2) ^ 2) :=
    ((contDiff_const.mul hP).add (hT.mul hQ)).div (hr.pow 2) hr0
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun w : (E n × ℝ) × E n =>
      sq (1 + w.1.2 * ((-2 * ⟪w.1.1, w.2⟫ + w.1.2 * ‖w.2‖ ^ 2) / sq (‖w.1.1‖ ^ 2) ^ 2))) :=
    sq_contDiff.comp (contDiff_const.add (hT.mul hv))
  have h2 : ∀ w : (E n × ℝ) × E n, 2 * (1 + sq (1 + w.1.2 *
      ((-2 * ⟪w.1.1, w.2⟫ + w.1.2 * ‖w.2‖ ^ 2) / sq (‖w.1.1‖ ^ 2) ^ 2))) ^ 2 ≠ 0 := by
    intro w; have := sq_pos (1 + w.1.2 *
      ((-2 * ⟪w.1.1, w.2⟫ + w.1.2 * ‖w.2‖ ^ 2) / sq (‖w.1.1‖ ^ 2) ^ 2)); positivity
  have h3 : ∀ w : (E n × ℝ) × E n, 2 * sq (‖w.1.1‖ ^ 2) ^ 2 ≠ 0 := by
    intro w; have := sq_pos (‖w.1.1‖ ^ 2); positivity
  exact hr.mul ((hQ.div (contDiff_const.mul (hr.pow 2)) h3).sub
    ((hv.pow 2).div (contDiff_const.mul ((contDiff_const.add hs).pow 2)) h2))

lemma bfun_contDiff_full :
    ContDiff ℝ (⊤ : ℕ∞) (fun w : (E n × ℝ) × E n => bfun w.1.1 w.2 w.1.2) := by
  unfold bfun
  exact ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp phaseErr_contDiff)).neg).cexp

lemma phase_alg (R r d P Q : ℝ) (hR : 1 ≤ R) (hr : 4 < r) (hd : 0 < d)
    (hd2 : d ^ 2 = r ^ 2 - 2 * R⁻¹ * P + R⁻¹ ^ 2 * Q) :
    R ^ 2 * d - r * (Q / (2 * r ^ 2) - ((-2 * P + R⁻¹ * Q) / r ^ 2) ^ 2 /
      (2 * (1 + d / r) ^ 2)) = R ^ 2 * r - R * P / r := by
  have hR0 : R ≠ 0 := by positivity
  have hr0 : r ≠ 0 := by positivity
  have hrd : r + d ≠ 0 := by positivity
  rw [show (1 + d / r) = (r + d) / r by field_simp]
  field_simp
  have hE : R ^ 2 * d ^ 2 - R ^ 2 * r ^ 2 + 2 * R * P - Q = 0 := by
    rw [hd2]; field_simp; ring
  linear_combination (2 * R ^ 2 * r * (r + d) - (Q - 2 * R * P)) * hE

lemma phase_id (R : ℝ) (hR : 1 ≤ R) (x y : E n) (hx : 4 < ‖x‖) (hy : ‖y‖ < 2) :
    R ^ 2 * ‖x - R⁻¹ • y‖ - phaseErr x y R⁻¹ = R ^ 2 * ‖x‖ - R * ⟪x, y⟫ / ‖x‖ := by
  have hR0 : 0 < R := by linarith
  set r := ‖x‖ with hr
  set d := ‖x - R⁻¹ • y‖ with hd
  have hsr : sq (r ^ 2) = r := by
    rw [sq_of_ge (by nlinarith), Real.sqrt_sq (by linarith)]
  have hd2 : d ^ 2 = r ^ 2 - 2 * R⁻¹ * ⟪x, y⟫ + R⁻¹ ^ 2 * ‖y‖ ^ 2 := by
    rw [hd, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hR0)]; ring
  have hRy : ‖R⁻¹ • y‖ < 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR0)]
    have : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
    nlinarith [norm_nonneg y]
  have hdr : r - 2 < d := by
    have := norm_sub_norm_le x (R⁻¹ • y); linarith
  have h1v : 1 + R⁻¹ * ((-2 * ⟪x, y⟫ + R⁻¹ * ‖y‖ ^ 2) / r ^ 2) = (d / r) ^ 2 := by
    rw [div_pow, hd2]; field_simp; ring
  have hss : sq (1 + R⁻¹ * ((-2 * ⟪x, y⟫ + R⁻¹ * ‖y‖ ^ 2) / r ^ 2)) = d / r := by
    rw [h1v, sq_of_ge, Real.sqrt_sq (by positivity)]
    rw [div_pow, le_div_iff₀ (by positivity)]; nlinarith
  unfold phaseErr
  rw [hsr, hss]
  exact phase_alg R r d _ _ hR (by linarith) (by linarith) hd2

/-! ## Step 1: rescaled Carleson–Sjölin -/

lemma kernelOp_K_eq (R : ℝ) (hR : 1 ≤ R) (g : E n → ℂ) (x : E n) :
    kernelOp (K n R) g x = ((R ^ n : ℝ) : ℂ) *
      carlesonSjolinOp (psi n) (R ^ 2) (fun y => (theta n (R • y) : ℂ) * g (R • y)) x := by
  have hR0 : 0 < R := by linarith
  simp only [carlesonSjolinOp, kernelOp]
  have hcs := Measure.integral_comp_smul (volume : Measure (E n)) (fun y => K n R x y * g y) R
  rw [finrank_euclideanSpace_fin, abs_of_pos (by positivity)] at hcs
  have hpt : (fun z : E n => K n R x (R • z) * g (R • z)) = fun z =>
      Complex.exp (2 * Real.pi * Complex.I * ((R ^ 2 * ‖x - z‖ : ℝ) : ℂ)) * (psi n x z : ℂ) *
        ((theta n (R • z) : ℂ) * g (R • z)) := by
    funext z
    by_cases h0 : theta n (R • z) = 0
    · simp [K, h0]
    have hz := theta_ne_zero h0
    have hz' : ‖z‖ ≤ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR0] at hz; nlinarith [norm_nonneg z]
    rw [K, psi, eta_eq_one hz', inv_smul_smul₀ hR0.ne']
    push_cast; ring
  rw [hpt] at hcs
  rw [hcs, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (by positivity),
    Complex.ofReal_one, one_mul]

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
            rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal (hM x y)
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
    have : 1 / p.toReal ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
    linarith
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
    gcongr
    · exact hD gs
    · exact (kernelOp_bound p hp hpt k hk M A hM hA _ hfg).trans (by gcongr)
  have h2 : eLpNorm g p volume ≤ eLpNorm f p volume + ENNReal.ofReal δ := by
    have : g = f - (f - g) := by abel
    rw [this]
    exact (eLpNorm_sub_le hf.1 hfg.1 hp).trans (by gcongr)
  calc eLpNorm (kernelOp k f) p volume
      ≤ D * (eLpNorm f p volume + ENNReal.ofReal δ) + L * ENNReal.ofReal δ :=
        h1.trans (by gcongr)
    _ = D * eLpNorm f p volume + (D + L) * ENNReal.ofReal δ := by ring
    _ ≤ D * eLpNorm f p volume + ε := by
        gcongr
        rw [← ENNReal.ofReal_toReal hDt, ← ENNReal.ofReal_toReal hLt,
          ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal]
        apply ENNReal.ofReal_le_ofReal
        rw [hδ, mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ ε := ε.2
        nlinarith [ENNReal.toReal_nonneg (a := D), ENNReal.toReal_nonneg (a := L)]

lemma norm_exp_two_pi_I (t : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1 := by
  rw [show 2 * Real.pi * Complex.I * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma K_continuous (R : ℝ) : Continuous (Function.uncurry (K n R)) := by
  have hc : Continuous (chi n) := chi_contDiff.continuous
  have ht : Continuous (theta n) := theta_contDiff.continuous
  unfold K Function.uncurry
  fun_prop
lemma norm_K_le (R : ℝ) (x y : E n) : ‖K n R x y‖ ≤ 1 := by
  rw [K, norm_mul, norm_exp_two_pi_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have := abs_chi_le x; have := abs_theta_le y
  nlinarith [abs_nonneg (chi n x), abs_nonneg (theta n y)]
lemma K_ne_zero (R : ℝ) {x y : E n} (h : K n R x y ≠ 0) : 4 < ‖x‖ ∧ ‖x‖ < 5 ∧ ‖y‖ < 2 := by
  have h' : chi n x * theta n y ≠ 0 := by
    intro h0; apply h; simp [K, h0]
  exact ⟨(chi_ne_zero (left_ne_zero_of_mul h')).1, (chi_ne_zero (left_ne_zero_of_mul h')).2,
    theta_ne_zero (right_ne_zero_of_mul h')⟩

lemma opNorm_K_le (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hp' : p ≤ ENNReal.ofReal (2 * n / (n + 1))) (α : ℝ) (hα : 0 ≤ α) (hBR : BR n p α) :
    ∃ C₀ : ℝ≥0, ∀ R : ℝ, 1 ≤ R → opNorm p p (kernelOp (K n R)) ≤
      C₀ * ENNReal.ofReal (R ^ (2 * α - n * (1 - p.toReal⁻¹))) := by
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hp'
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne'
  obtain ⟨C, hC⟩ := carlesonSjolinOp_le_of_br n hn p hp hp' α hα hBR (psi n) psi_contDiff
    psi_hasCompactSupport psi_sep
  have hconj : (conjExp p)⁻¹.toReal = 1 - p.toReal⁻¹ := by
    rw [conjExp, inv_inv, ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.2 hp) ENNReal.one_ne_top,
      ENNReal.toReal_one, ENNReal.toReal_inv]
  refine ⟨C, fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  apply opNorm_le_of_schwartz p hp hpt (K n R) (K_continuous R) 1 5 (norm_K_le R)
    (fun x y h => by have := K_ne_zero R h; exact ⟨this.2.1.le, by linarith [this.2.2]⟩)
    _ (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
  intro g
  set h : E n → ℂ := fun y => (theta n (R • y) : ℂ) * g (R • y) with hhdef
  have htc : HasCompactSupport (fun y : E n => (theta n (R • y) : ℂ)) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : E n) 2)
    intro y hy
    by_contra h0
    have h0' : theta n (R • y) ≠ 0 := fun e => h0 (by simp [e])
    have hz := theta_ne_zero h0'
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR0] at hz
    exact hy (by simp only [mem_closedBall, dist_zero_right]; nlinarith [norm_nonneg y])
  have hhc : HasCompactSupport h := htc.mul_right
  have hhs : ContDiff ℝ (⊤ : ℕ∞) h :=
    (Complex.ofRealCLM.contDiff.comp (theta_contDiff.comp (contDiff_const_smul R))).mul
      ((g.smooth ⊤).comp (contDiff_const_smul R))
  set hs : 𝓢(E n, ℂ) := hhc.toSchwartzMap hhs
  have hcoe : (hs : E n → ℂ) = h := rfl
  have h1 : kernelOp (K n R) g = ((R ^ n : ℝ) : ℂ) • carlesonSjolinOp (psi n) (R ^ 2) hs := by
    funext x; rw [kernelOp_K_eq R hR g x, hcoe]; rfl
  have h2 : eLpNorm h p volume ≤
      ENNReal.ofReal (R ^ (-((n : ℝ) / p.toReal))) * eLpNorm g p volume := by
    rw [← eLpNorm_comp_smul p hp0 hpt g R hR0]
    apply eLpNorm_mono
    intro y
    simp only [hhdef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_theta_le _)
  have h3 := hC (R ^ 2) (by nlinarith) hs
  rw [hcoe, hconj] at h3
  rw [h1, eLpNorm_const_smul, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hreal : R ^ n * (((R ^ 2) ^ (-((n : ℝ) * (1 - p.toReal⁻¹))) * (R ^ 2) ^ α) *
      R ^ (-((n : ℝ) / p.toReal))) = R ^ (2 * α - n * (1 - p.toReal⁻¹)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast R 2, ← Real.rpow_mul hR0.le,
      ← Real.rpow_mul hR0.le, ← Real.rpow_add hR0, ← Real.rpow_add hR0, ← Real.rpow_add hR0]
    congr 1; push_cast; ring
  calc ENNReal.ofReal (R ^ n) * eLpNorm (carlesonSjolinOp (psi n) (R ^ 2) hs) p volume
      ≤ ENNReal.ofReal (R ^ n) * (C * ENNReal.ofReal ((R ^ 2) ^ (-((n : ℝ) * (1 - p.toReal⁻¹)))) *
          ENNReal.ofReal ((R ^ 2) ^ α) *
          (ENNReal.ofReal (R ^ (-((n : ℝ) / p.toReal))) * eLpNorm g p volume)) := by
        gcongr
        exact h3.trans (by gcongr)
    _ = C * ENNReal.ofReal (R ^ n * (((R ^ 2) ^ (-((n : ℝ) * (1 - p.toReal⁻¹))) * (R ^ 2) ^ α) *
          R ^ (-((n : ℝ) / p.toReal)))) * eLpNorm g p volume := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]; ring
    _ = _ := by rw [hreal]

/-! ## Step 2: Lemma 2.1 -/

lemma bfun_measurable (τ : ℝ) : Measurable (Function.uncurry fun x y => bfun (n := n) x y τ) := by
  have h := (bfun_contDiff_full (n := n)).continuous.comp
    (show Continuous (fun z : E n × E n => ((z.1, τ), z.2)) by fun_prop)
  exact h.measurable
lemma norm_bfun (x y : E n) (τ : ℝ) : ‖bfun x y τ‖ ≤ 1 := by
  rw [bfun, show -(2 * Real.pi * Complex.I * ((phaseErr x y τ : ℝ) : ℂ)) =
    ((-(2 * Real.pi * phaseErr x y τ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]
lemma bfun_contDiff (y : E n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : E n × ℝ => bfun z.1 y z.2) := by
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun z : E n × ℝ => ((z, y) : (E n × ℝ) × E n)) :=
    contDiff_id.prodMk contDiff_const
  have h := ContDiff.comp (g := fun w : (E n × ℝ) × E n => bfun w.1.1 w.2 w.1.2)
    (f := fun z : E n × ℝ => ((z, y) : (E n × ℝ) × E n)) bfun_contDiff_full hi
  exact h
lemma bfun_der_bound (k : ℕ) : ∃ D : ℝ, ∀ y : E n, ‖y‖ ≤ 2 → ∀ z : E n × ℝ, ‖z‖ < 6 →
    ‖iteratedFDeriv ℝ k (fun z : E n × ℝ => bfun z.1 y z.2) z‖ ≤ D := by
  have hΦ := (bfun_contDiff_full (n := n))
  have hcont : Continuous (fun w => iteratedFDeriv ℝ k
      (fun w : (E n × ℝ) × E n => bfun w.1.1 w.2 w.1.2) w) :=
    hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : (E n × ℝ) × E n) 6).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨D, fun y hy z hz => ?_⟩
  set c : (E n × ℝ) × E n := (0, y)
  have hcomp : (fun z : E n × ℝ => bfun z.1 y z.2) =
      (fun w : (E n × ℝ) × E n => bfun (w + c).1.1 (w + c).2 (w + c).1.2) ∘
        (ContinuousLinearMap.inl ℝ (E n × ℝ) (E n)) := by
    funext z; simp [c]
  have hΦc : ContDiff ℝ (⊤ : ℕ∞)
      (fun w : (E n × ℝ) × E n => bfun (w + c).1.1 (w + c).2 (w + c).1.2) :=
    hΦ.comp (contDiff_id.add contDiff_const)
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ hΦc _ (by exact_mod_cast le_top)]
  have hshift := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun w : (E n × ℝ) × E n =>
      bfun w.1.1 w.2 w.1.2) k c ((ContinuousLinearMap.inl ℝ (E n × ℝ) (E n)) z)
  rw [hshift]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin k, ‖ContinuousLinearMap.inl ℝ (E n × ℝ) (E n)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inl_le_one _ _ _)
  have hmem : (ContinuousLinearMap.inl ℝ (E n × ℝ) (E n)) z + c ∈ closedBall 0 6 := by
    simp only [c, ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add,
      mem_closedBall, dist_zero_right, Prod.norm_def]
    exact max_le hz.le (by linarith)
  have := hD _ hmem
  calc _ ≤ ‖iteratedFDeriv ℝ k (fun w : (E n × ℝ) × E n => bfun w.1.1 w.2 w.1.2)
        ((ContinuousLinearMap.inl ℝ (E n × ℝ) (E n)) z + c)‖ * 1 := by
          gcongr
    _ ≤ D := by rw [mul_one]; exact this

lemma K_mul_bfun (R : ℝ) (hR : 1 ≤ R) (x y : E n) :
    K n R x y * bfun x y R⁻¹ = K' n R x y := by
  by_cases h0 : chi n x * theta n y = 0
  · simp [K, K', h0]
  have hx := chi_ne_zero (left_ne_zero_of_mul h0)
  have hy := theta_ne_zero (right_ne_zero_of_mul h0)
  rw [K, K', bfun, mul_right_comm, ← Complex.exp_add, ← phase_id R hR x y hx.1 hy]
  congr 2
  push_cast; ring

lemma opNorm_K'_le (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hp' : p ≤ ENNReal.ofReal (2 * n / (n + 1))) (α : ℝ) (hα : 0 ≤ α) (hBR : BR n p α) :
    ∃ D : ℝ≥0, ∃ R₁ : ℝ, 1 ≤ R₁ ∧ ∀ R : ℝ, R₁ ≤ R → opNorm p p (kernelOp (K' n R)) ≤
      D * ENNReal.ofReal (R ^ (2 * α - n * (1 - p.toReal⁻¹))) := by
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hp'
  have hp1 : 1 ≤ p.toReal := by
    have := (ENNReal.toReal_le_toReal (by simp) hpt).2 hp; simpa using this
  have hn0 : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨C₀, hC₀⟩ := opNorm_K_le hn p hp hp' α hα hBR
  have hL := opNorm_le_of_contDiff n p p hp hp (K n) (closedBall 0 5 ×ˢ closedBall 0 2)
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)) 1
    (fun R => (K_continuous R).measurable)
    (fun R x y => ⟨norm_K_le R x y, fun h => by
      have := K_ne_zero R h
      exact ⟨by simpa using this.2.1.le, by simpa using this.2.2.le⟩⟩)
    bfun bfun_measurable 1 norm_bfun (1 / 2) (by norm_num) (ball (0 : E n × ℝ) 6) isOpen_ball
    (by
      rintro ⟨x, τ⟩ ⟨⟨⟨x', y'⟩, ⟨hx', -⟩, rfl⟩, hτ⟩
      simp only [mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs]
      simp only [mem_closedBall, dist_zero_right] at hx'
      have := hτ.1; have := hτ.2
      exact max_lt (by linarith) (by rw [abs_lt]; constructor <;> linarith))
    (fun y _ => (bfun_contDiff y).contDiffOn)
    (by
      intro k
      obtain ⟨D, hD⟩ := bfun_der_bound (n := n) k
      refine ⟨D, ?_⟩
      rintro y ⟨⟨x', y'⟩, ⟨-, hy'⟩, rfl⟩ z hz
      rw [iteratedFDerivWithin_of_isOpen k isOpen_ball hz]
      simp only [mem_closedBall, dist_zero_right] at hy'
      exact hD y' hy' z (by simpa using hz))
  obtain ⟨C, R₀, hCR⟩ := hL n hn0
  refine ⟨C.toNNReal * C₀ + C.toNNReal, max R₀ 1, le_max_right _ _, fun R hR => ?_⟩
  have hR1 : 1 ≤ R := le_trans (le_max_right _ _) hR
  have hR0 : 0 < R := by linarith
  have hker : (kernelOp fun x y => K n R x y * bfun x y R⁻¹) = kernelOp (K' n R) := by
    congr 1; funext x y; exact K_mul_bfun R hR1 x y
  have h1 := hCR R (le_trans (le_max_left _ _) hR)
  rw [hker] at h1
  have hexp : R ^ (-(n : ℝ)) ≤ R ^ (2 * α - n * (1 - p.toReal⁻¹)) := by
    apply Real.rpow_le_rpow_of_exponent_le hR1
    have : 0 < p.toReal⁻¹ := by positivity
    nlinarith
  refine h1.trans ?_
  rw [ENNReal.ofReal_mul' (by positivity)]
  calc ENNReal.ofReal C * opNorm p p (kernelOp (K n R)) +
        ENNReal.ofReal C * ENNReal.ofReal (R ^ (-(n : ℝ)))
      ≤ ENNReal.ofReal C * (C₀ * ENNReal.ofReal (R ^ (2 * α - n * (1 - p.toReal⁻¹)))) +
        ENNReal.ofReal C * ENNReal.ofReal (R ^ (2 * α - n * (1 - p.toReal⁻¹))) := by
        gcongr
        exact hC₀ R hR1
    _ = ((C.toNNReal * C₀ + C.toNNReal : ℝ≥0) : ℝ≥0∞) *
          ENNReal.ofReal (R ^ (2 * α - n * (1 - p.toReal⁻¹))) := by
        rw [ENNReal.ofReal]; push_cast; ring

/-! ## Step 3: evaluation on `f(R ·)` and polar coordinates -/

lemma norm_kernelOp_K' (R : ℝ) (hR : 1 ≤ R) (f : 𝓢(E n, ℂ))
    (hf : tsupport f ⊆ closedBall 0 R) (x : E n) :
    ‖kernelOp (K' n R) (fun y => f (R • y)) x‖ =
      |chi n x| * (R ^ n)⁻¹ * ‖𝓕 (f : E n → ℂ) (‖x‖⁻¹ • x)‖ := by
  have hR0 : 0 < R := by linarith
  set u : E n := ‖x‖⁻¹ • x with hu
  have hθ : ∀ y : E n, (theta n y : ℂ) * f (R • y) = f (R • y) := by
    intro y
    by_cases hf0 : f (R • y) = 0
    · simp [hf0]
    have hm : R • y ∈ closedBall (0 : E n) R := hf (subset_tsupport _ hf0)
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR0] at hm
    have : ‖y‖ ≤ 1 := by nlinarith [norm_nonneg y]
    rw [theta_eq_one this]; simp
  set c : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((R ^ 2 * ‖x‖ : ℝ) : ℂ)) * (chi n x : ℂ)
  have hint : ∀ y : E n, K' n R x y * f (R • y) = c *
      (Complex.exp (((-2 * Real.pi * ⟪R • y, u⟫ : ℝ) : ℂ) * Complex.I) • f (R • y)) := by
    intro y
    have hin : R * ⟪x, y⟫ / ‖x‖ = ⟪R • y, u⟫ := by
      rw [hu, real_inner_smul_left, real_inner_smul_right, real_inner_comm]; ring
    rw [K', hin, smul_eq_mul]
    conv_rhs => rw [← hθ y]
    rw [show 2 * Real.pi * Complex.I * ((R ^ 2 * ‖x‖ - ⟪R • y, u⟫ : ℝ) : ℂ) =
      2 * Real.pi * Complex.I * ((R ^ 2 * ‖x‖ : ℝ) : ℂ) +
        ((-2 * Real.pi * ⟪R • y, u⟫ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_add]
    simp only [c]; push_cast; ring
  have hk : kernelOp (K' n R) (fun y => f (R • y)) x =
      c * (|(R ^ Module.finrank ℝ (E n))⁻¹| • 𝓕 (f : E n → ℂ) u) := by
    simp only [kernelOp]
    rw [funext hint, integral_const_mul]
    congr 1
    rw [Real.fourier_eq']
    exact Measure.integral_comp_smul volume (fun v : E n =>
      Complex.exp (((-2 * Real.pi * ⟪v, u⟫ : ℝ) : ℂ) * Complex.I) • f v) R
  rw [hk, norm_mul, norm_smul, finrank_euclideanSpace_fin]
  simp only [c, norm_mul, norm_exp_two_pi_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  simp [abs_of_pos hR0, mul_assoc]

lemma polar (hn : 2 ≤ n) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ F : E n → ℝ≥0∞, Measurable F →
    ∫⁻ x, Set.indicator {x : E n | 4.2 < ‖x‖ ∧ ‖x‖ < 4.8} (fun x => F (‖x‖⁻¹ • x)) x =
      c * ∫⁻ ω, F ω ∂(sphereMeasure n) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  set e := homeomorphUnitSphereProd (E n)
  set I : Set (Set.Ioi (0 : ℝ)) := {r | 4.2 < r.1 ∧ r.1 < 4.8} with hI
  have hIm : MeasurableSet I :=
    (measurableSet_Ioo (a := (4.2 : ℝ)) (b := 4.8)).preimage measurable_subtype_coe
  have hmp := (volume : Measure (E n)).measurePreserving_homeomorphUnitSphereProd
  rw [finrank_euclideanSpace_fin] at hmp
  have key : ∀ F : E n → ℝ≥0∞, Measurable F →
      ∫⁻ x, Set.indicator {x : E n | 4.2 < ‖x‖ ∧ ‖x‖ < 4.8} (fun x => F (‖x‖⁻¹ • x)) x =
        Measure.volumeIoiPow (n - 1) I * ∫⁻ ω, F ω ∂(sphereMeasure n) := by
    intro F hF
    set G := Set.indicator {x : E n | 4.2 < ‖x‖ ∧ ‖x‖ < 4.8} (fun x => F (‖x‖⁻¹ • x))
    have hsupp : Function.support G ⊆ ({0}ᶜ : Set (E n)) := by
      intro x hx
      have := Set.support_indicator_subset hx
      intro h0; simp only [Set.mem_singleton_iff] at h0; subst h0
      simp at this; linarith [this.1]
    rw [← setLIntegral_eq_of_support_subset hsupp,
      ← lintegral_subtype_comap (measurableSet_singleton _).compl]
    have h2 := hmp.lintegral_comp_emb e.measurableEmbedding (fun y => G (e.symm y))
    refine Eq.trans ?_ (h2.trans ?_)
    · simp only [e, Homeomorph.symm_apply_apply]
    have h3 : ∀ y : sphere (0 : E n) 1 × Set.Ioi (0 : ℝ),
        G (e.symm y) = F y.1 * I.indicator 1 y.2 := by
      rintro ⟨ω, r⟩
      have hω : ‖(ω : E n)‖ = 1 := by simp
      have hr : 0 < r.1 := r.2
      have hn : ‖r.1 • (ω : E n)‖ = r.1 := by rw [norm_smul, hω, mul_one, Real.norm_of_nonneg hr.le]
      simp only [G, e, homeomorphUnitSphereProd_symm_apply_coe, Set.indicator, Set.mem_setOf_eq,
        hn, hI, Pi.one_apply]
      split_ifs <;> simp [smul_smul, inv_mul_cancel₀ hr.ne']
    simp_rw [h3]
    rw [lintegral_prod_mul (f := fun ω : sphere (0 : E n) 1 => F ω) (g := I.indicator 1) (hF.comp measurable_subtype_coe).aemeasurable
      ((measurable_one.indicator hIm).aemeasurable), lintegral_indicator_one hIm, mul_comm]
    rfl
  refine ⟨Measure.volumeIoiPow (n - 1) I, ?_, ?_, key⟩
  · -- the value at `F = 1`
    have h1 := key (fun _ => 1) measurable_const
    simp only [lintegral_const, one_mul] at h1
    have hpos : 0 < (volume : Measure (E n)) {x : E n | 4.2 < ‖x‖ ∧ ‖x‖ < 4.8} := by
      apply IsOpen.measure_pos
      · exact (isOpen_lt continuous_const continuous_norm).inter
          (isOpen_lt continuous_norm continuous_const)
      · refine ⟨(4.5 : ℝ) • EuclideanSpace.single ⟨0, by omega⟩ 1, ?_⟩
        simp [norm_smul]; norm_num
    intro h0
    rw [lintegral_indicator_const (by
      exact ((isOpen_lt continuous_const continuous_norm).inter
          (isOpen_lt continuous_norm continuous_const)).measurableSet), one_mul, h0,
      zero_mul] at h1
    exact hpos.ne' h1
  · have h1 := key (fun _ => 1) measurable_const
    simp only [lintegral_const, one_mul] at h1
    have hm : MeasurableSet {x : E n | 4.2 < ‖x‖ ∧ ‖x‖ < 4.8} :=
      ((isOpen_lt continuous_const continuous_norm).inter
          (isOpen_lt continuous_norm continuous_const)).measurableSet
    rw [lintegral_indicator_const hm, one_mul] at h1
    have hfin : (volume : Measure (E n)) {x : E n | 4.2 < ‖x‖ ∧ ‖x‖ < 4.8} < ⊤ := by
      refine lt_of_le_of_lt (measure_mono (t := ball 0 5) ?_) measure_ball_lt_top
      intro x hx; simp only [Set.mem_setOf_eq] at hx; simp; linarith [hx.2]
    intro htop
    rw [htop, ENNReal.top_mul] at h1
    · exact hfin.ne h1
    · simp only [sphereMeasure]
      simp
      exact ⟨by omega, (measure_ball_pos _ _ one_pos).ne'⟩

lemma eLpNorm_le_opNorm {p : ℝ≥0∞} {T : (E n → ℂ) → (E n → ℂ)} {D : ℝ≥0∞}
    (hT : opNorm p p T ≤ D) (hD : D ≠ ⊤) (h0 : T 0 = 0) {f : E n → ℂ} (hf : MemLp f p volume) :
    eLpNorm (T f) p volume ≤ D * eLpNorm f p volume := by
  have hlt : sInf {C : ℝ≥0∞ | ∀ f : E n → ℂ, MemLp f p volume →
      eLpNorm (T f) p volume ≤ C * eLpNorm f p volume} < ⊤ := lt_of_le_of_lt hT (lt_top_iff_ne_top.2 hD)
  obtain ⟨C₁, hC₁, -⟩ := sInf_lt_iff.1 hlt
  by_cases hz : eLpNorm f p volume = 0
  · have := hC₁ f hf; rw [hz, mul_zero] at this; rw [hz, mul_zero]; exact this
  have hft : eLpNorm f p volume ≠ ⊤ := hf.eLpNorm_ne_top
  have : eLpNorm (T f) p volume / eLpNorm f p volume ≤ opNorm p p T := by
    apply le_sInf
    intro C hC
    exact (ENNReal.div_le_iff hz hft).2 (hC f hf)
  exact (ENNReal.div_le_iff hz hft).1 (this.trans hT)

/-- The lower bound for `K' R` applied to `f(R ·)`. -/
lemma restriction_le_kernelOp_K' (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(E n, ℂ),
      tsupport f ⊆ closedBall 0 R →
      c * eLpNorm (restriction (f : E n → ℂ)) p (sphereMeasure n) ≤
        ENNReal.ofReal (R ^ n) * eLpNorm (kernelOp (K' n R) (fun y => f (R • y))) p volume := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  obtain ⟨c₀, hc0, hct, hpol⟩ := polar hn
  refine ⟨c₀ ^ (1 / p.toReal), ?_, ?_, ?_⟩
  · exact (ENNReal.rpow_pos (pos_iff_ne_zero.2 hc0) hct).ne'
  · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hct
  intro R hR f hf
  have hR0 : 0 < R := by linarith
  have hcont : Continuous (𝓕 (f : E n → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 f).continuous
  set F : E n → ℝ≥0∞ := fun ω => ‖𝓕 (f : E n → ℂ) ω‖ₑ ^ p.toReal with hFdef
  have hFm : Measurable F := (hcont.enorm.measurable).pow_const _
  set a : ℝ≥0∞ := ENNReal.ofReal ((R ^ n)⁻¹) with ha
  have hlow : ∀ x : E n, a ^ p.toReal *
      Set.indicator {x : E n | 4.2 < ‖x‖ ∧ ‖x‖ < 4.8} (fun x => F (‖x‖⁻¹ • x)) x ≤
      ‖kernelOp (K' n R) (fun y => f (R • y)) x‖ₑ ^ p.toReal := by
    intro x
    by_cases hx : x ∈ {x : E n | 4.2 < ‖x‖ ∧ ‖x‖ < 4.8}
    · rw [Set.indicator_of_mem hx, ← ofReal_norm_eq_enorm, norm_kernelOp_K' R hR f hf,
        chi_eq_one hx.1.le hx.2.le, abs_one, one_mul, ENNReal.ofReal_mul (by positivity),
        ENNReal.mul_rpow_of_nonneg _ _ hq.le, ofReal_norm_eq_enorm]
    · rw [Set.indicator_of_notMem hx, mul_zero]; exact bot_le
  have hX : eLpNorm (restriction (f : E n → ℂ)) p (sphereMeasure n) =
      (∫⁻ ω, F ω ∂(sphereMeasure n)) ^ (1 / p.toReal) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]; rfl
  have hK : (a ^ p.toReal * (c₀ * ∫⁻ ω, F ω ∂(sphereMeasure n))) ^ (1 / p.toReal) ≤
      eLpNorm (kernelOp (K' n R) (fun y => f (R • y))) p volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, ← hpol F hFm, ← lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top)]
    gcongr with x
    exact hlow x
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one, ← hX] at hK
  calc c₀ ^ (1 / p.toReal) * eLpNorm (restriction (f : E n → ℂ)) p (sphereMeasure n)
      = ENNReal.ofReal (R ^ n) * (a * (c₀ ^ (1 / p.toReal) *
          eLpNorm (restriction (f : E n → ℂ)) p (sphereMeasure n))) := by
        rw [ha, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
          ENNReal.ofReal_one, one_mul]
    _ ≤ _ := by gcongr

end RTB

theorem restr_two_mul_of_br_dev (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hp' : p ≤ ENNReal.ofReal (2 * n / (n + 1))) (α : ℝ) (hα : 0 ≤ α) :
    BR n p α → Restr n p (2 * α) := by
  intro hBR
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hp'
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne'
  obtain ⟨D, R₁, hR₁, hD⟩ := RTB.opNorm_K'_le hn p hp hp' α hα hBR
  obtain ⟨c, hc0, hct, hc⟩ := RTB.restriction_le_kernelOp_K' hn p hp hpt
  refine ⟨(c⁻¹ * D * ENNReal.ofReal (R₁ ^ (2 * α))).toNNReal, ?_⟩
  intro R hR f hf
  set R' := max R R₁ with hR'
  have hR'1 : 1 ≤ R' := le_trans hR (le_max_left _ _)
  have hR'0 : 0 < R' := lt_of_lt_of_le one_pos hR'1
  have hfR' : tsupport f ⊆ closedBall 0 R' :=
    hf.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hmem : MemLp (fun y => f (R' • y)) p volume := by
    refine ⟨(f.continuous.comp (continuous_const_smul R')).aestronglyMeasurable, ?_⟩
    rw [RTB.eLpNorm_comp_smul p hp0 hpt _ R' hR'0]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp p volume).eLpNorm_lt_top
  have h0 : kernelOp (RTB.K' n R') 0 = 0 := by
    funext x; simp [kernelOp]
  have key2 := RTB.eLpNorm_le_opNorm (hD R' (le_max_right _ _))
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) h0 hmem
  rw [RTB.eLpNorm_comp_smul p hp0 hpt _ R' hR'0] at key2
  have key1 := hc R' hR'1 f hfR'
  have hY : eLpNorm (f : E n → ℂ) p (volume.restrict (closedBall 0 R)) =
      eLpNorm (f : E n → ℂ) p volume :=
    eLpNorm_restrict_eq_of_support_subset ((subset_tsupport _).trans hf)
  rw [hY]
  set X := eLpNorm (restriction (f : E n → ℂ)) p (sphereMeasure n)
  set Y := eLpNorm (f : E n → ℂ) p volume
  have hreal : R' ^ n * (R' ^ (2 * α - n * (1 - p.toReal⁻¹)) * R' ^ (-((n : ℝ) / p.toReal))) =
      R' ^ (2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR'0, ← Real.rpow_add hR'0]
    congr 1; ring
  have hcX : c * X ≤ D * ENNReal.ofReal (R' ^ (2 * α)) * Y := by
    calc c * X ≤ ENNReal.ofReal (R' ^ n) * (D * ENNReal.ofReal
          (R' ^ (2 * α - n * (1 - p.toReal⁻¹))) * (ENNReal.ofReal
            (R' ^ (-((n : ℝ) / p.toReal))) * Y)) := key1.trans (by gcongr)
      _ = D * ENNReal.ofReal (R' ^ n * (R' ^ (2 * α - n * (1 - p.toReal⁻¹)) *
            R' ^ (-((n : ℝ) / p.toReal)))) * Y := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]; ring
      _ = D * ENNReal.ofReal (R' ^ (2 * α)) * Y := by rw [hreal]
  have hR'α : R' ^ (2 * α) ≤ R₁ ^ (2 * α) * R ^ (2 * α) := by
    rw [← Real.mul_rpow (by linarith) (by linarith)]
    apply Real.rpow_le_rpow hR'0.le _ (by linarith)
    rcases le_total R R₁ with h | h
    · rw [hR', max_eq_right h]; nlinarith
    · rw [hR', max_eq_left h]; nlinarith
  have hfin : c⁻¹ * D * ENNReal.ofReal (R₁ ^ (2 * α)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) ENNReal.coe_ne_top)
      ENNReal.ofReal_ne_top
  rw [ENNReal.coe_toNNReal hfin]
  calc X = c⁻¹ * (c * X) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
    _ ≤ c⁻¹ * (D * ENNReal.ofReal (R' ^ (2 * α)) * Y) := by gcongr
    _ ≤ c⁻¹ * (D * ENNReal.ofReal (R₁ ^ (2 * α) * R ^ (2 * α)) * Y) := by
        gcongr
    _ = c⁻¹ * D * ENNReal.ofReal (R₁ ^ (2 * α)) * ENNReal.ofReal (R ^ (2 * α)) * Y := by
        rw [ENNReal.ofReal_mul (by positivity)]; ring

end TaoBR

theorem solution : type_of% @TaoBR.restr_two_mul_of_br_dev := @TaoBR.restr_two_mul_of_br_dev

-- Prove2me | solution 1 for TeschlQM.Atomic.atomicHamiltonian_isBoundedBelow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T10:47:48.596744+00:00
-- url     : https://prove2.me/submissions/bd42cf51-771c-48e2-9786-ad95436b023b

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian

/-! Child C1 of 7ab9d8bf (HVZ): the atomic Hamiltonian is bounded below.
Hardy's inequality in each electron coordinate (dilation argument on Schwartz functions, Plancherel for
derivatives, density of Schwartz functions in the graph norm of H0, Fatou) + Coulomb AM-GM bound. -/

set_option autoImplicit false

/-! Hardy inequality pieces for 7ab9d8bf (HVZ C1). -/


open MeasureTheory SchwartzMap FourierTransform LineDeriv

namespace HVZHardy

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- H2: Plancherel for a directional derivative of a Schwartz function. -/
theorem integral_norm_sq_lineDeriv (f : 𝓢(V, ℂ)) (m : V) :
    ∫ x, ‖fderiv ℝ f x m‖ ^ 2 =
      ∫ ξ, (2 * Real.pi * inner ℝ ξ m) ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
  have h1 := integral_norm_sq_fourier (∂_{m} f)
  rw [fourier_lineDerivOp_eq] at h1
  have hg : (inner ℝ · m : V → ℝ).HasTemperateGrowth := ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [← integral_congr_ae (Filter.Eventually.of_forall fun x => by
      rw [← lineDerivOp_apply_eq_fderiv] : ∀ᵐ x ∂volume, ‖(∂_{m} f) x‖ ^ 2 = ‖fderiv ℝ f x m‖ ^ 2),
    ← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_apply, smulLeftCLM_apply_apply hg, norm_smul, Complex.norm_mul,
    Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- H1a scaling: in dimension 3, `∫ |f(s y)|²/|y|² = s⁻¹ ∫ |f|²/|y|²`. -/
theorem integral_scale (hV : Module.finrank ℝ V = 3) (f : V → ℂ) {s : ℝ} (hs : 0 < s) :
    ∫ y, ‖f (s • y)‖ ^ 2 / ‖y‖ ^ 2 = s⁻¹ * ∫ y, ‖f y‖ ^ 2 / ‖y‖ ^ 2 := by
  have h := Measure.integral_comp_smul (volume : Measure V) (fun y => ‖f y‖ ^ 2 / ‖y‖ ^ 2) s
  rw [hV] at h
  have e : ∀ y : V, ‖f (s • y)‖ ^ 2 / ‖y‖ ^ 2 = s ^ 2 * (‖f (s • y)‖ ^ 2 / ‖s • y‖ ^ 2) := by
    intro y
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    rcases eq_or_ne ‖y‖ 0 with hy | hy
    · simp [hy]
    · field_simp
  simp_rw [e]
  rw [integral_const_mul, h, smul_eq_mul, abs_of_pos (by positivity)]
  field_simp

/-- Radial integrability in a 3-dimensional space: `‖x‖^s e^{-b‖x‖}` for `s > -3`. -/
lemma integrable_radial (hV : Module.finrank ℝ V = 3) (s : ℝ) (hs : -3 < s) (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : V => ‖x‖ ^ s * Real.exp (-(b * ‖x‖))) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hV]; norm_num)
  refine (integrable_fun_norm_addHaar volume (f := fun y : ℝ => y ^ s * Real.exp (-(b * y)))).2 ?_
  refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := s + 2) (p := 1) (by linarith) one_pos hb).congr_fun
    (fun y hy => ?_) measurableSet_Ioi
  have hy' : 0 < y := hy
  beta_reduce
  rw [hV, Real.rpow_one, Real.rpow_add hy', Real.rpow_two, smul_eq_mul]
  norm_num
  ring

/-- `‖y‖^s (1+‖y‖)^{-4}` is integrable in dimension 3 for `-3 < s ≤ 0`. -/
lemma integrable_rpow_decay (hV : Module.finrank ℝ V = 3) (s : ℝ) (hs : -3 < s) (hs0 : s ≤ 0) :
    Integrable (fun y : V => ‖y‖ ^ s * ((1 + ‖y‖) ^ 4)⁻¹) := by
  have h1 := (integrable_radial hV s hs 1 one_pos).const_mul (Real.exp 1)
  have h2 : Integrable (fun y : V => (1 + ‖y‖) ^ (-(4:ℝ))) :=
    integrable_one_add_norm (by rw [hV]; norm_num)
  refine (h1.add h2).mono' (Measurable.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun y => ?_)
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
  have e4 : (1 + ‖y‖) ^ (-(4:ℝ)) = ((1 + ‖y‖) ^ 4)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]; norm_cast
  have hs' : 0 ≤ ‖y‖ ^ s := Real.rpow_nonneg hy0 s
  have hinv0 : 0 ≤ ((1 + ‖y‖) ^ 4)⁻¹ := by positivity
  simp only [Pi.add_apply, e4]
  rw [Real.norm_of_nonneg (by positivity)]
  rcases le_or_gt ‖y‖ 1 with h | h
  · have hinv : ((1 + ‖y‖) ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    have he : 1 ≤ Real.exp 1 * Real.exp (-(1 * ‖y‖)) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    calc ‖y‖ ^ s * ((1 + ‖y‖) ^ 4)⁻¹ ≤ ‖y‖ ^ s * 1 := mul_le_mul_of_nonneg_left hinv hs'
      _ ≤ ‖y‖ ^ s * (Real.exp 1 * Real.exp (-(1 * ‖y‖))) := mul_le_mul_of_nonneg_left he hs'
      _ ≤ _ := le_add_of_le_of_nonneg (le_of_eq (by ring)) hinv0
  · have hle : ‖y‖ ^ s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h.le hs0
    refine le_add_of_nonneg_of_le (by positivity) ?_
    calc ‖y‖ ^ s * ((1 + ‖y‖) ^ 4)⁻¹ ≤ 1 * ((1 + ‖y‖) ^ 4)⁻¹ := mul_le_mul_of_nonneg_right hle hinv0
      _ = _ := one_mul _

/-- Schwartz decay with an explicit power of `1 + ‖x‖`. -/
lemma exists_decay {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (g : 𝓢(D, F)) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x, (1 + ‖x‖) ^ k * ‖g x‖ ≤ C := by
  have h : ∀ x, (1 + ‖x‖) ^ k * ‖g x‖ ≤
      2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g := fun x => by
    simpa [norm_iteratedFDeriv_zero] using
      one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl g x
  exact ⟨_, le_trans (by positivity) (h 0), h⟩

lemma inv_one_add_smul_le (y : V) {s : ℝ} (hs : 1 / 2 < s) :
    ((1 + ‖s • y‖) ^ 4)⁻¹ ≤ 16 * ((1 + ‖y‖) ^ 4)⁻¹ := by
  have hle : (1 + ‖y‖) / 2 ≤ 1 + ‖s • y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    nlinarith [norm_nonneg y]
  have h4 : ((1 + ‖y‖) / 2) ^ 4 ≤ (1 + ‖s • y‖) ^ 4 := pow_le_pow_left₀ (by positivity) hle 4
  calc ((1 + ‖s • y‖) ^ 4)⁻¹ ≤ (((1 + ‖y‖) / 2) ^ 4)⁻¹ := inv_anti₀ (by positivity) h4
    _ = 16 * ((1 + ‖y‖) ^ 4)⁻¹ := by rw [div_pow, inv_div, div_eq_mul_inv]; norm_num

lemma sq_le_decay (a C r : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) (h : (1 + r) ^ 2 * a ≤ C) :
    a ^ 2 ≤ C ^ 2 * ((1 + r) ^ 4)⁻¹ := by
  have h0 : 0 ≤ (1 + r) ^ 2 * a := by positivity
  have := pow_le_pow_left₀ h0 h 2
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  nlinarith [this]

lemma mul_le_decay (a b C D r : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (h : (1 + r) ^ 2 * a ≤ C) (h' : (1 + r) ^ 2 * b ≤ D) :
    a * b ≤ C * D * ((1 + r) ^ 4)⁻¹ := by
  have := mul_le_mul h h' (by positivity) (le_trans (by positivity) h)
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  nlinarith [this]

/-- H1a: Hardy's inequality in a 3-dimensional space, for a function with explicit decay. -/
theorem hardy3_of_decay (hV : Module.finrank ℝ V = 3) (f : V → ℂ) (hd : Differentiable ℝ f)
    (hDc : Continuous (fun y => fderiv ℝ f y)) (C1 C2 : ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (h1 : ∀ x, (1 + ‖x‖) ^ 2 * ‖f x‖ ≤ C1) (h2 : ∀ x, (1 + ‖x‖) ^ 2 * ‖fderiv ℝ f x‖ ≤ C2) :
    Integrable (fun y : V => ‖f y‖ ^ 2 / ‖y‖ ^ 2) ∧
    ∫ y, ‖f y‖ ^ 2 / ‖y‖ ^ 2 ≤ 4 * ∫ y, ‖fderiv ℝ f y‖ ^ 2 := by
  have hfc : Continuous (fun y => f y) := hd.continuous
  -- integrability of the two sides
  have hI : Integrable (fun y : V => ‖f y‖ ^ 2 / ‖y‖ ^ 2) := by
    refine ((integrable_rpow_decay hV (-2) (by norm_num) (by norm_num)).const_mul (C1 ^ 2)).mono'
      (Measurable.aestronglyMeasurable (by fun_prop)) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg (norm_nonneg y), Real.rpow_two]
    have := sq_le_decay _ _ _ (norm_nonneg _) (norm_nonneg y) (h1 y)
    calc ‖f y‖ ^ 2 / ‖y‖ ^ 2 = ‖f y‖ ^ 2 * (‖y‖ ^ 2)⁻¹ := div_eq_mul_inv _ _
      _ ≤ C1 ^ 2 * ((1 + ‖y‖) ^ 4)⁻¹ * (‖y‖ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  have hJ : Integrable (fun y : V => ‖fderiv ℝ f y‖ ^ 2) := by
    refine ((integrable_rpow_decay hV 0 (by norm_num) le_rfl).const_mul (C2 ^ 2)).mono'
      (Measurable.aestronglyMeasurable (by fun_prop)) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_zero, one_mul]
    exact sq_le_decay _ _ _ (norm_nonneg _) (norm_nonneg y) (h2 y)
  -- differentiate the dilation family at s = 1
  set I := ∫ y, ‖f y‖ ^ 2 / ‖y‖ ^ 2 with hIdef
  let F : ℝ → V → ℝ := fun s y => ‖f (s • y)‖ ^ 2 / ‖y‖ ^ 2
  let F' : ℝ → V → ℝ := fun s y => 2 * inner ℝ (f (s • y)) (fderiv ℝ f (s • y) y) / ‖y‖ ^ 2
  let bound : V → ℝ := fun y => 32 * C1 * C2 * (‖y‖ ^ (-1:ℝ) * ((1 + ‖y‖) ^ 4)⁻¹)
  have hbound : Integrable bound :=
    (integrable_rpow_decay hV (-1) (by norm_num) (by norm_num)).const_mul _
  have hF'meas : AEStronglyMeasurable (F' 1) volume := by
    refine Measurable.aestronglyMeasurable ?_
    have : Continuous (fun y : V => 2 * inner ℝ (f ((1:ℝ) • y)) (fderiv ℝ f ((1:ℝ) • y) y)) := by
      fun_prop
    exact this.measurable.div (by fun_prop)
  obtain ⟨hF'int, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := F) (F' := F') (x₀ := (1:ℝ)) (bound := bound) (Ioi_mem_nhds (by norm_num : (1/2:ℝ) < 1))
    (Filter.Eventually.of_forall fun s => Measurable.aestronglyMeasurable
      (((hfc.comp (continuous_const_smul s)).measurable.norm.pow_const 2).div
        (measurable_norm.pow_const 2)))
    (by simpa only [F, one_smul] using hI) hF'meas
    (Filter.Eventually.of_forall fun y s hs => by
      have hs' : (1/2:ℝ) < s := hs
      simp only [F', bound]
      rcases eq_or_ne y 0 with hy | hy
      · subst hy; simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, div_zero, norm_zero]
        have : (0:ℝ) ^ (-1:ℝ) = 0 := by rw [Real.zero_rpow (by norm_num)]
        rw [this]; simp
      have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have hin : |inner ℝ (f (s • y)) (fderiv ℝ f (s • y) y)| ≤
          ‖f (s • y)‖ * (‖fderiv ℝ f (s • y)‖ * ‖y‖) :=
        (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left ((fderiv ℝ f (s • y)).le_opNorm y) (norm_nonneg _))
      have hfd := mul_le_decay _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
        (h1 (s • y)) (h2 (s • y))
      have h16 := inv_one_add_smul_le y hs'
      rw [Real.rpow_neg_one, Real.norm_eq_abs, abs_div, abs_mul, abs_two,
        abs_of_pos (by positivity : (0:ℝ) < ‖y‖ ^ 2), div_le_iff₀ (by positivity)]
      have hP : ‖f (s • y)‖ * ‖fderiv ℝ f (s • y)‖ ≤ C1 * C2 * (16 * ((1 + ‖y‖) ^ 4)⁻¹) :=
        hfd.trans (mul_le_mul_of_nonneg_left h16 (by positivity))
      have e : 32 * C1 * C2 * (‖y‖⁻¹ * ((1 + ‖y‖) ^ 4)⁻¹) * ‖y‖ ^ 2 =
          2 * (C1 * C2 * (16 * ((1 + ‖y‖) ^ 4)⁻¹)) * ‖y‖ := by
        field_simp; ring
      rw [e]
      have := mul_le_mul_of_nonneg_right hP hr.le
      nlinarith [hin, this])
    hbound
    (Filter.Eventually.of_forall fun y s _ => by
      have hc : HasDerivAt (fun s : ℝ => s • y) y s := by
        simpa using (hasDerivAt_id s).smul_const y
      have hf : HasDerivAt (fun s => f (s • y)) (fderiv ℝ f (s • y) y) s :=
        ((hd _).hasFDerivAt).comp_hasDerivAt s hc
      exact hf.norm_sq.div_const _)
  have hG : HasDerivAt (fun s : ℝ => s⁻¹ * I) (-I) 1 := by
    simpa using (hasDerivAt_inv one_ne_zero).mul_const I
  have heq : (fun s => ∫ y, F s y) =ᶠ[nhds 1] fun s => s⁻¹ * I := by
    filter_upwards [lt_mem_nhds one_pos] with s hs
    exact integral_scale hV f hs
  have hval : ∫ y, F' 1 y = -I := hderiv.unique (hG.congr_of_eventuallyEq heq)
  refine ⟨hI, ?_⟩
  have hpt : ∀ y, -F' 1 y ≤ ‖f y‖ ^ 2 / ‖y‖ ^ 2 / 2 + 2 * ‖fderiv ℝ f y‖ ^ 2 := by
    intro y
    simp only [F', one_smul]
    rcases eq_or_ne y 0 with hy | hy
    · subst hy; simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, div_zero, neg_zero, zero_div, zero_add]
      positivity
    have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hin : -inner ℝ (f y) (fderiv ℝ f y y) ≤ ‖f y‖ * (‖fderiv ℝ f y‖ * ‖y‖) :=
      (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left ((fderiv ℝ f y).le_opNorm y) (norm_nonneg _)))
    have e : ‖f y‖ ^ 2 / ‖y‖ ^ 2 / 2 + 2 * ‖fderiv ℝ f y‖ ^ 2 =
        (‖f y‖ ^ 2 / 2 + 2 * ‖fderiv ℝ f y‖ ^ 2 * ‖y‖ ^ 2) / ‖y‖ ^ 2 := by
      field_simp
    rw [e, ← neg_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg (‖f y‖ - 2 * ‖fderiv ℝ f y‖ * ‖y‖)]
  have hle := integral_mono hF'int.neg ((hI.div_const 2).add (hJ.const_mul 2)) hpt
  simp only [Pi.neg_apply, Pi.add_apply] at hle
  rw [integral_neg, hval, neg_neg, integral_add (hI.div_const 2) (hJ.const_mul 2), integral_div,
    integral_const_mul] at hle
  linarith

/-- H1a for Schwartz functions. -/
theorem hardy3 (hV : Module.finrank ℝ V = 3) (f : 𝓢(V, ℂ)) :
    Integrable (fun y : V => ‖f y‖ ^ 2 / ‖y‖ ^ 2) ∧
    ∫ y, ‖f y‖ ^ 2 / ‖y‖ ^ 2 ≤ 4 * ∫ y, ‖fderiv ℝ f y‖ ^ 2 := by
  obtain ⟨C1, hC1, h1⟩ := exists_decay f 2
  obtain ⟨C2, hC2, h2⟩ := exists_decay (fderivCLM ℝ V ℂ f) 2
  simp only [fderivCLM_apply] at h2
  have hDc : Continuous (fun y => fderiv ℝ (⇑f) y) := by
    have := (fderivCLM ℝ V ℂ f).continuous
    simpa only [funext (fderivCLM_apply (𝕜 := ℝ) f)] using this
  exact hardy3_of_decay hV f f.differentiable hDc C1 C2 hC1 hC2 h1 h2

/-- Hardy along an isometric affine 3-dimensional slice of a Schwartz function. -/
theorem hardy_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hV : Module.finrank ℝ V = 3) (φ : 𝓢(E, ℂ)) (L : V →L[ℝ] E) (hL : ∀ y, ‖L y‖ = ‖y‖) (c : E) :
    Integrable (fun y : V => ‖φ (c + L y)‖ ^ 2 / ‖y‖ ^ 2) ∧
    Integrable (fun y : V => ‖fderiv ℝ (⇑φ) (c + L y)‖ ^ 2) ∧
    ∫ y, ‖φ (c + L y)‖ ^ 2 / ‖y‖ ^ 2 ≤ 4 * ∫ y, ‖fderiv ℝ (⇑φ) (c + L y)‖ ^ 2 := by
  obtain ⟨C1, hC1, h1⟩ := exists_decay φ 2
  obtain ⟨C2, hC2, h2⟩ := exists_decay (fderivCLM ℝ E ℂ φ) 2
  simp only [fderivCLM_apply] at h2
  have hDφ : Continuous (fun x => fderiv ℝ (⇑φ) x) := by
    have := (fderivCLM ℝ E ℂ φ).continuous
    simpa only [funext (fderivCLM_apply (𝕜 := ℝ) φ)] using this
  have hgd : ∀ y, HasFDerivAt (fun y => φ (c + L y)) ((fderiv ℝ (⇑φ) (c + L y)).comp L) y :=
    fun y => (φ.differentiableAt.hasFDerivAt).comp y (L.hasFDerivAt.const_add c)
  have hfd : ∀ y, fderiv ℝ (fun y => φ (c + L y)) y = (fderiv ℝ (⇑φ) (c + L y)).comp L :=
    fun y => (hgd y).fderiv
  have hLn : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun y => by rw [hL, one_mul])
  have hcomp : ∀ y, ‖(fderiv ℝ (⇑φ) (c + L y)).comp L‖ ≤ ‖fderiv ℝ (⇑φ) (c + L y)‖ := fun y =>
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa using mul_le_mul_of_nonneg_left hLn (norm_nonneg (fderiv ℝ (⇑φ) (c + L y))))
  have hgrow : ∀ y : V, (1 + ‖y‖) ^ 2 ≤ (1 + ‖c‖) ^ 2 * (1 + ‖c + L y‖) ^ 2 := by
    intro y
    have h3 : ‖y‖ ≤ ‖c + L y‖ + ‖c‖ := by
      rw [← hL y]
      calc ‖L y‖ = ‖(c + L y) - c‖ := by simp
        _ ≤ _ := norm_sub_le _ _
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity)
      (by nlinarith [mul_nonneg (norm_nonneg c) (norm_nonneg (c + L y))]) 2
  have h1' : ∀ y : V, (1 + ‖y‖) ^ 2 * ‖φ (c + L y)‖ ≤ (1 + ‖c‖) ^ 2 * C1 := fun y => calc
      (1 + ‖y‖) ^ 2 * ‖φ (c + L y)‖ ≤ (1 + ‖c‖) ^ 2 * (1 + ‖c + L y‖) ^ 2 * ‖φ (c + L y)‖ :=
        mul_le_mul_of_nonneg_right (hgrow y) (norm_nonneg _)
      _ = (1 + ‖c‖) ^ 2 * ((1 + ‖c + L y‖) ^ 2 * ‖φ (c + L y)‖) := by ring
      _ ≤ (1 + ‖c‖) ^ 2 * C1 := mul_le_mul_of_nonneg_left (h1 _) (by positivity)
  have hD' : ∀ y : V, (1 + ‖y‖) ^ 2 * ‖fderiv ℝ (⇑φ) (c + L y)‖ ≤ (1 + ‖c‖) ^ 2 * C2 := fun y => calc
      (1 + ‖y‖) ^ 2 * ‖fderiv ℝ (⇑φ) (c + L y)‖ ≤
          (1 + ‖c‖) ^ 2 * (1 + ‖c + L y‖) ^ 2 * ‖fderiv ℝ (⇑φ) (c + L y)‖ :=
        mul_le_mul_of_nonneg_right (hgrow y) (norm_nonneg _)
      _ = (1 + ‖c‖) ^ 2 * ((1 + ‖c + L y‖) ^ 2 * ‖fderiv ℝ (⇑φ) (c + L y)‖) := by ring
      _ ≤ (1 + ‖c‖) ^ 2 * C2 := mul_le_mul_of_nonneg_left (h2 _) (by positivity)
  have h2' : ∀ y : V, (1 + ‖y‖) ^ 2 * ‖fderiv ℝ (fun y => φ (c + L y)) y‖ ≤ (1 + ‖c‖) ^ 2 * C2 :=
    fun y => by
      rw [hfd]
      exact le_trans (mul_le_mul_of_nonneg_left (hcomp y) (by positivity)) (hD' y)
  have hgc : Continuous (fun y => fderiv ℝ (fun y => φ (c + L y)) y) := by
    simp_rw [hfd]
    exact (hDφ.comp (continuous_const.add L.continuous)).clm_comp continuous_const
  obtain ⟨hI, hle⟩ := hardy3_of_decay hV (fun y => φ (c + L y)) (fun y => (hgd y).differentiableAt)
    hgc _ _ (by positivity) (by positivity) h1' h2'
  have hJ : Integrable (fun y : V => ‖fderiv ℝ (⇑φ) (c + L y)‖ ^ 2) := by
    have hc : Continuous (fun y : V => ‖fderiv ℝ (⇑φ) (c + L y)‖ ^ 2) :=
      ((hDφ.comp (continuous_const.add L.continuous)).norm).pow 2
    refine ((integrable_rpow_decay hV 0 (by norm_num) le_rfl).const_mul
      (((1 + ‖c‖) ^ 2 * C2) ^ 2)).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_zero, one_mul]
    exact sq_le_decay _ _ _ (norm_nonneg _) (norm_nonneg y) (hD' y)
  refine ⟨hI, hJ, hle.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))⟩
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity) hJ
    (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [hfd]
  exact pow_le_pow_left₀ (norm_nonneg _) (hcomp y) 2

end HVZHardy

/-! ## H1b: lift to the electron coordinate of `ℝ^{3N}` -/

namespace HVZHardy

variable {N : ℕ} (j : Fin N)

/-- The coordinates not belonging to electron `j`. -/
abbrev Kj := {p : Fin N × Fin 3 // p.1 ≠ j}

/-- Split the coordinates into those of electron `j` and the rest. -/
def splitEquiv : Fin N × Fin 3 ≃ Kj j ⊕ Fin 3 where
  toFun p := if h : p.1 = j then Sum.inr p.2 else Sum.inl ⟨p, h⟩
  invFun := Sum.elim Subtype.val (fun a => (j, a))
  left_inv p := by
    by_cases h : p.1 = j
    · simp only [dif_pos h, Sum.elim_inr]; exact Prod.ext h.symm rfl
    · simp only [dif_neg h, Sum.elim_inl]
  right_inv s := by
    rcases s with ⟨p, hp⟩ | a
    · exact dif_neg hp
    · exact dif_pos rfl

/-- Insert the electron-`j` coordinates `y` into the rest `w`. -/
noncomputable def ins (w : Kj j → ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin N × Fin 3) :=
  WithLp.toLp 2 (fun p => if h : p.1 = j then y p.2 else w ⟨p, h⟩)

noncomputable def insE : (Kj j → ℝ) × EuclideanSpace ℝ (Fin 3) ≃ᵐ EuclideanSpace ℝ (Fin N × Fin 3) :=
  ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Kj j ⊕ Fin 3 => ℝ)).symm).trans
    ((MeasurableEquiv.arrowCongr' (splitEquiv j).symm (MeasurableEquiv.refl ℝ)).trans
      (MeasurableEquiv.toLp 2 (Fin N × Fin 3 → ℝ)))

lemma insE_apply (w : Kj j → ℝ) (y : EuclideanSpace ℝ (Fin 3)) : insE j (w, y) = ins j w y := by
  ext p
  simp [insE, ins, MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr, splitEquiv,
    MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi]
  split_ifs <;> rfl

lemma insE_mp : MeasurePreserving (insE j) := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Kj j → ℝ))
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm) (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3))
  have h2 : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : Kj j ⊕ Fin 3 => ℝ)).symm
      (volume.prod volume) volume :=
    measurePreserving_sumPiEquivProdPi_symm (fun _ => volume)
  have h3 : MeasurePreserving (MeasurableEquiv.arrowCongr' (splitEquiv j).symm (MeasurableEquiv.refl ℝ)) :=
    volume_preserving_arrowCongr' _ _ (MeasurePreserving.id volume)
  have h4 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin N × Fin 3 → ℝ)) :=
    MeasurePreserving.symm _ (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin N × Fin 3))
  exact h4.comp (h3.comp (h2.comp h1))

lemma ins_split (w : Kj j → ℝ) (y : EuclideanSpace ℝ (Fin 3)) : ins j w y = ins j w 0 + ins j 0 y := by
  ext p
  simp only [ins, PiLp.add_apply]
  split_ifs <;> simp

/-- The linear isometric embedding of the electron-`j` coordinates. -/
noncomputable def insL : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin N × Fin 3) :=
  LinearMap.toContinuousLinearMap
    { toFun := ins j 0
      map_add' := fun a b => by ext p; simp only [ins, PiLp.add_apply]; split_ifs <;> simp
      map_smul' := fun r a => by ext p; simp only [ins, PiLp.smul_apply]; split_ifs <;> simp }

lemma insL_apply (y : EuclideanSpace ℝ (Fin 3)) : insL j y = ins j 0 y := rfl

lemma norm_insL (y : EuclideanSpace ℝ (Fin 3)) : ‖insL j y‖ = ‖y‖ := by
  rw [insL_apply, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fintype.sum_prod_type]
  congr 1
  simp [ins]

/-- H1b: Hardy's inequality in the electron-`j` coordinate for a Schwartz function on `ℝ^{3N}`. -/
theorem hardy_electron (φ : 𝓢(EuclideanSpace ℝ (Fin N × Fin 3), ℂ)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin N × Fin 3) =>
      ‖φ x‖ ^ 2 / ‖(WithLp.toLp 2 (fun a => x (j, a)) : EuclideanSpace ℝ (Fin 3))‖ ^ 2) ∧
    ∫ x : EuclideanSpace ℝ (Fin N × Fin 3),
      ‖φ x‖ ^ 2 / ‖(WithLp.toLp 2 (fun a => x (j, a)) : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ≤
      4 * ∫ x, ‖fderiv ℝ (⇑φ) x‖ ^ 2 := by
  have hV : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  set F : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ := fun x =>
    ‖φ x‖ ^ 2 / ‖(WithLp.toLp 2 (fun a => x (j, a)) : EuclideanSpace ℝ (Fin 3))‖ ^ 2 with hF
  set D : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ := fun x => ‖fderiv ℝ (⇑φ) x‖ ^ 2 with hDdef
  have hmp := insE_mp j
  have hel : ∀ w y, (WithLp.toLp 2 (fun a => (ins j w y) (j, a)) : EuclideanSpace ℝ (Fin 3)) = y := by
    intro w y; ext a; simp [ins]
  have hFslice : ∀ w y, F (insE j (w, y)) = ‖φ (ins j w 0 + insL j y)‖ ^ 2 / ‖y‖ ^ 2 := by
    intro w y; simp only [hF, insE_apply, hel, insL_apply, ← ins_split]
  have hDslice : ∀ w y, D (insE j (w, y)) = ‖fderiv ℝ (⇑φ) (ins j w 0 + insL j y)‖ ^ 2 := by
    intro w y; simp only [hDdef, insE_apply, insL_apply, ← ins_split]
  -- integrability of D on ℝ^{3N}
  obtain ⟨C2, hC2, h2⟩ := exists_decay (fderivCLM ℝ _ ℂ φ) 0
  simp only [fderivCLM_apply, pow_zero, one_mul] at h2
  have hDφ : Continuous (fun x => fderiv ℝ (⇑φ) x) := by
    have := (fderivCLM ℝ (EuclideanSpace ℝ (Fin N × Fin 3)) ℂ φ).continuous
    simpa only [funext (fderivCLM_apply (𝕜 := ℝ) φ)] using this
  have hDint : Integrable D := by
    have hi := ((fderivCLM ℝ (EuclideanSpace ℝ (Fin N × Fin 3)) ℂ φ).integrable (μ := volume)).norm.const_mul C2
    refine hi.mono' (hDφ.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    show ‖fderiv ℝ (⇑φ) x‖ ^ 2 ≤ _
    rw [sq, fderivCLM_apply]
    exact mul_le_mul_of_nonneg_right (h2 x) (norm_nonneg _)
  have hFm : Measurable F := by
    have : Measurable (fun x : EuclideanSpace ℝ (Fin N × Fin 3) => ‖φ x‖ ^ 2) :=
      (φ.continuous.norm.pow 2).measurable
    refine this.div ((Continuous.measurable ?_).pow_const 2)
    fun_prop
  have hDP : Integrable (D ∘ insE j) := (hmp.integrable_comp_emb (insE j).measurableEmbedding).2 hDint
  have hGm : AEStronglyMeasurable (F ∘ insE j) (volume.prod volume) :=
    (hFm.comp (insE j).measurable).aestronglyMeasurable
  have hsl := fun w : Kj j → ℝ => hardy_slice hV φ (insL j) (norm_insL j) (ins j w 0)
  have hGP : Integrable (F ∘ insE j) (volume.prod volume) := by
    refine (integrable_prod_iff hGm).2 ⟨Filter.Eventually.of_forall fun w => ?_, ?_⟩
    · simpa only [Function.comp, hFslice] using (hsl w).1
    · refine (hDP.integral_prod_left.const_mul 4).mono' hGm.norm.integral_prod_right'
        (Filter.Eventually.of_forall fun w => ?_)
      simp only [Function.comp, hFslice, hDslice]
      rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      simp only [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ‖φ (ins j w 0 + insL j _)‖ ^ 2 / ‖_‖ ^ 2)]
      exact (hsl w).2.2
  refine ⟨(hmp.integrable_comp_emb (insE j).measurableEmbedding).1 hGP, ?_⟩
  rw [← hmp.integral_comp' (g := F), ← hmp.integral_comp' (g := D)]
  change ∫ q, (F ∘ insE j) q ∂(volume.prod volume) ≤ 4 * ∫ q, (D ∘ insE j) q ∂(volume.prod volume)
  rw [integral_prod _ hGP, integral_prod _ hDP, ← integral_const_mul]
  refine integral_mono hGP.integral_prod_left (hDP.integral_prod_left.const_mul 4) fun w => ?_
  simp only [Function.comp, hFslice, hDslice]
  exact (hsl w).2.2

end HVZHardy


/-! H2-sum and H3 density for the Hardy step of 7ab9d8bf (HVZ C1). -/


open MeasureTheory SchwartzMap FourierTransform LineDeriv
open scoped ContDiff InnerProductSpace ComplexConjugate Topology
open Filter

namespace HVZDens

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- copied from 7ab9d8bf_hardy.lean -/
theorem integral_norm_sq_lineDeriv (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (m : EuclideanSpace ℝ ι) :
    ∫ x, ‖fderiv ℝ f x m‖ ^ 2 =
      ∫ ξ, (2 * Real.pi * inner ℝ ξ m) ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
  have h1 := integral_norm_sq_fourier (∂_{m} f)
  rw [fourier_lineDerivOp_eq] at h1
  have hg : (inner ℝ · m : EuclideanSpace ℝ ι → ℝ).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [← integral_congr_ae (Filter.Eventually.of_forall fun x => by
      rw [← lineDerivOp_apply_eq_fderiv] : ∀ᵐ x ∂volume, ‖(∂_{m} f) x‖ ^ 2 = ‖fderiv ℝ f x m‖ ^ 2),
    ← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_apply, smulLeftCLM_apply_apply hg, norm_smul, Complex.norm_mul,
    Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

lemma sq_fourier_lineDeriv (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (m ξ : EuclideanSpace ℝ ι) :
    ‖𝓕 (∂_{m} f) ξ‖ ^ 2 = (2 * Real.pi * inner ℝ ξ m) ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
  have hg : (inner ℝ · m : EuclideanSpace ℝ ι → ℝ).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [fourier_lineDerivOp_eq]
  simp only [smul_apply, smulLeftCLM_apply_apply hg, norm_smul, Complex.norm_mul,
    Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

lemma opNorm_sq_le_sum (L : EuclideanSpace ℝ ι →L[ℝ] ℂ) :
    ‖L‖ ^ 2 ≤ ∑ i, ‖L (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
  set S := ∑ i, ‖L (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hb : ‖L‖ ≤ Real.sqrt S := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
    have hv : L v = ∑ i, v i • L (EuclideanSpace.single i (1 : ℝ)) := by
      conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v]
      simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
    rw [hv]
    calc ‖∑ i, v i • L (EuclideanSpace.single i (1 : ℝ))‖
        ≤ ∑ i, ‖v i‖ * ‖L (EuclideanSpace.single i (1 : ℝ))‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp only [norm_smul]
      _ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) * Real.sqrt S := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = Real.sqrt S * ‖v‖ := by rw [EuclideanSpace.norm_eq, mul_comm]
  calc ‖L‖ ^ 2 ≤ Real.sqrt S ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = S := Real.sq_sqrt hS0

/-- H2-sum: `∫ ‖Dφ‖² ≤ ∫ 4π²‖ξ‖² |𝓕φ|²` for Schwartz `φ`. -/
theorem h2sum (φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    ∫ x, ‖fderiv ℝ (⇑φ) x‖ ^ 2 ≤ ∫ ξ, 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 φ ξ‖ ^ 2 := by
  have hint : ∀ i : ι,
      Integrable (fun x => ‖fderiv ℝ (⇑φ) x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
    intro i
    set g := ∂_{EuclideanSpace.single i (1 : ℝ)} φ
    have := (memLp_two_iff_integrable_sq_norm g.continuous.aestronglyMeasurable).1 (g.memLp 2)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [g, lineDerivOp_apply_eq_fderiv]
  have hint2 : ∀ i : ι, Integrable (fun ξ : EuclideanSpace ℝ ι =>
      (2 * Real.pi * inner ℝ ξ (EuclideanSpace.single i (1 : ℝ))) ^ 2 * ‖𝓕 φ ξ‖ ^ 2) := by
    intro i
    set g := 𝓕 (∂_{EuclideanSpace.single i (1 : ℝ)} φ)
    have := (memLp_two_iff_integrable_sq_norm g.continuous.aestronglyMeasurable).1 (g.memLp 2)
    refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
    exact sq_fourier_lineDeriv φ _ ξ
  have hpt : ∀ ξ : EuclideanSpace ℝ ι, 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 φ ξ‖ ^ 2 =
      ∑ i, (2 * Real.pi * inner ℝ ξ (EuclideanSpace.single i (1 : ℝ))) ^ 2 * ‖𝓕 φ ξ‖ ^ 2 := by
    intro ξ
    rw [← Finset.sum_mul, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.inner_single_right]
    simp only [Real.norm_eq_abs, sq_abs, one_mul, conj_trivial]
    ring
  calc ∫ x, ‖fderiv ℝ (⇑φ) x‖ ^ 2
      ≤ ∫ x, ∑ i, ‖fderiv ℝ (⇑φ) x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
          (integrable_finsetSum _ fun i _ => hint i)
          (Filter.Eventually.of_forall fun x => opNorm_sq_le_sum _)
    _ = ∑ i, ∫ x, ‖fderiv ℝ (⇑φ) x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
        integral_finsetSum _ fun i _ => hint i
    _ = ∑ i, ∫ ξ, (2 * Real.pi * inner ℝ ξ (EuclideanSpace.single i (1 : ℝ))) ^ 2 *
          ‖𝓕 φ ξ‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => integral_norm_sq_lineDeriv φ _
    _ = ∫ ξ, 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 φ ξ‖ ^ 2 := by
        rw [← integral_finsetSum _ fun i _ => hint2 i]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => (hpt ξ).symm)

/-- the multiplier `1/(1+4π²‖ξ‖²)` is smooth -/
lemma contDiff_r : ContDiff ℝ ∞ (fun ξ : EuclideanSpace ℝ ι =>
    (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ)) := by
  have h1 : ContDiff ℝ ∞ (fun ξ : EuclideanSpace ℝ ι => 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) :=
    contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ))
  have h2 := h1.inv (fun ξ => by positivity)
  exact Complex.ofRealCLM.contDiff.comp h2

lemma contDiff_wr : ContDiff ℝ ∞ (fun ξ : EuclideanSpace ℝ ι =>
    ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ)) := by
  have h0 : ContDiff ℝ ∞ (fun ξ : EuclideanSpace ℝ ι => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_norm_sq ℝ))
  exact h0.mul contDiff_r

/-- H3: approximation of `G ∈ L²` with `4π²‖ξ‖² G ∈ L²` by Schwartz `g` in the graph norm. -/
theorem approx (G : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))
    (hW : MemLp (fun ξ : EuclideanSpace ℝ ι =>
      ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * (G : EuclideanSpace ℝ ι → ℂ) ξ) 2 volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : 𝓢(EuclideanSpace ℝ ι, ℂ), ∃ hg : MemLp (fun ξ : EuclideanSpace ℝ ι =>
      ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * g ξ) 2 volume,
      ‖g.toLp 2 (volume : Measure (EuclideanSpace ℝ ι)) - G‖ ≤ ε ∧ ‖hg.toLp _ - hW.toLp _‖ ≤ ε := by
  set H : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)) := G + hW.toLp _ with hHdef
  obtain ⟨k, hk1, hk2, hk3⟩ := MemLp.exist_eLpNorm_sub_le (μ := volume) (p := 2) (by norm_num)
    (by norm_num) (Lp.memLp H) hε
  set r : EuclideanSpace ℝ ι → ℂ := fun ξ => (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) with hr
  set w : EuclideanSpace ℝ ι → ℂ := fun ξ => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) with hw
  have hg1 : HasCompactSupport (k * r) := hk1.mul_right
  have hg2 : ContDiff ℝ ∞ (k * r) := hk2.mul contDiff_r
  have hh1 : HasCompactSupport (k * (w * r)) := hk1.mul_right
  have hh2 : ContDiff ℝ ∞ (k * (w * r)) := hk2.mul contDiff_wr
  set g := hg1.toSchwartzMap hg2 with hgdef
  set h := hh1.toSchwartzMap hh2 with hhdef
  have hgc : ∀ ξ, g ξ = k ξ * r ξ := fun ξ => rfl
  have hhc : ∀ ξ, h ξ = k ξ * (w ξ * r ξ) := fun ξ => rfl
  have hwg : (fun ξ : EuclideanSpace ℝ ι => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * g ξ) = ⇑h := by
    funext ξ; rw [hgc, hhc]; simp only [hw]; ring
  have hgm : MemLp (fun ξ : EuclideanSpace ℝ ι =>
      ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * g ξ) 2 volume := by
    rw [hwg]; exact h.memLp 2
  set K : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)) := (hk1.toSchwartzMap hk2).toLp 2
  have hKH : ‖K - H‖ ≤ ε := by
    rw [norm_sub_rev, Lp.norm_def]
    have hae : ((H - K : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
        EuclideanSpace ℝ ι → ℂ) =ᵐ[volume] (H : EuclideanSpace ℝ ι → ℂ) - k := by
      filter_upwards [Lp.coeFn_sub H K, (hk1.toSchwartzMap hk2).coeFn_toLp 2 volume]
        with ξ h1 h2
      rw [h1, Pi.sub_apply, Pi.sub_apply, h2]; rfl
    rw [eLpNorm_congr_ae hae]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hk3
  -- pointwise identities
  have hHpt : ∀ᵐ ξ ∂(volume : Measure (EuclideanSpace ℝ ι)),
      (K - H : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) ξ =
        k ξ - (1 + w ξ) * (G : EuclideanSpace ℝ ι → ℂ) ξ := by
    filter_upwards [Lp.coeFn_sub K H, (hk1.toSchwartzMap hk2).coeFn_toLp 2 volume,
      Lp.coeFn_add G (hW.toLp _), hW.coeFn_toLp] with ξ h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, hHdef, h3, Pi.add_apply, h4]
    simp only [hw]; change k ξ - _ = _; ring
  have hra : ∀ ξ, r ξ * (1 + w ξ) = 1 := by
    intro ξ; simp only [hr, hw]
    have : (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) ≠ 0 := by positivity
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_mul, inv_mul_cancel₀ this]
  have hrn : ∀ ξ, ‖r ξ‖ ≤ 1 := by
    intro ξ; simp only [hr, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ‖ξ‖, Real.pi_pos])
  have hwrn : ∀ ξ, ‖w ξ * r ξ‖ ≤ 1 := by
    intro ξ; simp only [hr, hw, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
    have hp : 0 < 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
    rw [abs_of_nonneg (by positivity), ← div_eq_mul_inv, div_le_one hp]
    linarith
  refine ⟨g, hgm, ?_, ?_⟩
  · refine (Lp.norm_le_norm_of_ae_le ?_).trans hKH
    filter_upwards [hHpt, Lp.coeFn_sub (g.toLp 2 (volume : Measure (EuclideanSpace ℝ ι))) G, g.coeFn_toLp 2 volume] with ξ h1 h2 h3
    rw [h1, h2, Pi.sub_apply, h3, hgc]
    have : k ξ * r ξ - (G : EuclideanSpace ℝ ι → ℂ) ξ =
        r ξ * (k ξ - (1 + w ξ) * (G : EuclideanSpace ℝ ι → ℂ) ξ) := by
      linear_combination (G : EuclideanSpace ℝ ι → ℂ) ξ * hra ξ
    rw [this, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hrn ξ)
  · refine (Lp.norm_le_norm_of_ae_le ?_).trans hKH
    filter_upwards [hHpt, Lp.coeFn_sub (hgm.toLp _) (hW.toLp _), hgm.coeFn_toLp, hW.coeFn_toLp]
      with ξ h1 h2 h3 h4
    rw [h1, h2, Pi.sub_apply, h3, h4, hgc]
    have : w ξ * (k ξ * r ξ) - w ξ * (G : EuclideanSpace ℝ ι → ℂ) ξ =
        (w ξ * r ξ) * (k ξ - (1 + w ξ) * (G : EuclideanSpace ℝ ι → ℂ) ξ) := by
      linear_combination w ξ * (G : EuclideanSpace ℝ ι → ℂ) ξ * hra ξ
    rw [this, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hwrn ξ)

open TeschlQM.Atomic in
/-- H4: extension of a Schwartz form bound `∫|φ|²V ≤ 4∫‖Dφ‖²` to `ψ ∈ 𝔇(H₀)` (density + Fatou). -/
theorem hardy_ext (V : EuclideanSpace ℝ ι → ℝ) (hVm : Measurable V) (hV0 : ∀ x, 0 ≤ V x)
    (hS : ∀ φ : 𝓢(EuclideanSpace ℝ ι, ℂ), Integrable (fun x => ‖φ x‖ ^ 2 * V x) ∧
      ∫ x, ‖φ x‖ ^ 2 * V x ≤ 4 * ∫ x, ‖fderiv ℝ (⇑φ) x‖ ^ 2)
    (ψ : (freeHamiltonian ι).domain) :
    Integrable (fun x => ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) x‖ ^ 2 * V x) ∧
      ∫ x, ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) x‖ ^ 2 * V x ≤
        4 * (⟪(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))), freeHamiltonian ι ψ⟫_ℂ).re := by
  set U := Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ
  obtain ⟨x, hx⟩ := ψ
  have hdom : MemLp (fun ξ : EuclideanSpace ℝ ι =>
      ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * (U x : EuclideanSpace ℝ ι → ℂ) ξ) 2 volume :=
    Submodule.mem_comap.1 hx
  have hval : freeHamiltonian ι ⟨x, hx⟩ = U.symm (hdom.toLp _) := rfl
  have hQ : (⟪x, freeHamiltonian ι ⟨x, hx⟩⟫_ℂ) = ⟪U x, hdom.toLp _⟫_ℂ := by
    rw [hval, ← U.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
  show Integrable (fun y => ‖x y‖ ^ 2 * V y) ∧
    ∫ y, ‖x y‖ ^ 2 * V y ≤ 4 * (⟪x, freeHamiltonian ι ⟨x, hx⟩⟫_ℂ).re
  rw [hQ]
  have hex : ∀ n : ℕ, ∃ g : 𝓢(EuclideanSpace ℝ ι, ℂ), ∃ hg : MemLp (fun ξ : EuclideanSpace ℝ ι =>
      ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * g ξ) 2 volume,
      ‖g.toLp 2 (volume : Measure (EuclideanSpace ℝ ι)) - U x‖ ≤ 1 / ((n : ℝ) + 1) ∧
        ‖hg.toLp _ - hdom.toLp _‖ ≤ 1 / ((n : ℝ) + 1) :=
    fun n => approx (U x) hdom (by positivity)
  choose g hg hg1 hg2 using hex
  let φ : ℕ → 𝓢(EuclideanSpace ℝ ι, ℂ) := fun n => 𝓕⁻ (g n)
  have hFφ : ∀ n, 𝓕 (φ n) = g n := fun n => fourier_fourierInv_eq (g n)
  have hUφ : ∀ n, U ((φ n).toLp 2 (volume : Measure (EuclideanSpace ℝ ι))) =
      (g n).toLp 2 (volume : Measure (EuclideanSpace ℝ ι)) := by
    intro n
    have := SchwartzMap.toLp_fourier_eq (φ n)
    rw [hFφ] at this
    exact this
  have hconv : Tendsto (fun n => (φ n).toLp 2 (volume : Measure (EuclideanSpace ℝ ι))) atTop
      (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [← U.norm_map, map_sub, hUφ]
    exact hg1 n
  have hQconv : Tendsto (fun n => ⟪(g n).toLp 2 (volume : Measure (EuclideanSpace ℝ ι)),
      (hg n).toLp _⟫_ℂ) atTop (𝓝 ⟪U x, hdom.toLp _⟫_ℂ) := by
    refine Filter.Tendsto.inner ?_ ?_
    · rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun n => norm_nonneg _) hg1 tendsto_one_div_add_atTop_nhds_zero_nat
    · rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun n => norm_nonneg _) hg2 tendsto_one_div_add_atTop_nhds_zero_nat
  have hQn : ∀ n, ∫ ξ, 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 (φ n) ξ‖ ^ 2 =
      (⟪(g n).toLp 2 (volume : Measure (EuclideanSpace ℝ ι)), (hg n).toLp _⟫_ℂ).re := by
    intro n
    rw [hFφ, L2.inner_def]
    have hre := integral_re (𝕜 := ℂ) (L2.integrable_inner
      ((g n).toLp 2 (volume : Measure (EuclideanSpace ℝ ι))) ((hg n).toLp _))
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    refine integral_congr_ae ?_
    filter_upwards [(g n).coeFn_toLp 2 volume, (hg n).coeFn_toLp] with ξ h1 h2
    rw [h1, h2, RCLike.inner_apply']
    have : (starRingEnd ℂ) (g n ξ) * (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * g n ξ) =
        ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖g n ξ‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_left_comm, Complex.conj_mul']; push_cast; ring
    rw [this, Complex.ofReal_re]
  have hQre : Tendsto (fun n => (⟪(g n).toLp 2 (volume : Measure (EuclideanSpace ℝ ι)),
      (hg n).toLp _⟫_ℂ).re) atTop (𝓝 (⟪U x, hdom.toLp _⟫_ℂ).re) :=
    (Complex.continuous_re.tendsto _).comp hQconv
  have hQ0 : 0 ≤ (⟪U x, hdom.toLp _⟫_ℂ).re :=
    ge_of_tendsto' hQre fun n => by
      rw [← hQn n]; exact integral_nonneg fun ξ => by positivity
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ ι)),
      ∀ n, ((φ n).toLp 2 (volume : Measure (EuclideanSpace ℝ ι))) y = φ n y :=
    ae_all_iff.2 fun n => (φ n).coeFn_toLp 2 volume
  have hnn : ∀ y, 0 ≤ ‖x y‖ ^ 2 * V y := fun y => mul_nonneg (sq_nonneg _) (hV0 y)
  have hlim : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ ι)),
      Tendsto (fun i => ENNReal.ofReal (‖φ (ns i) y‖ ^ 2 * V y)) atTop
        (𝓝 (ENNReal.ofReal (‖x y‖ ^ 2 * V y))) := by
    filter_upwards [hae, hcoe] with y h1 h2
    simp only [h2] at h1
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((h1.norm.pow 2).mul_const (V y))
  have hFn : ∀ n, ∫⁻ y, ENNReal.ofReal (‖φ n y‖ ^ 2 * V y) ≤
      ENNReal.ofReal (4 * (⟪(g n).toLp 2 (volume : Measure (EuclideanSpace ℝ ι)),
        (hg n).toLp _⟫_ℂ).re) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hS (φ n)).1
      (ae_of_all _ fun y => mul_nonneg (sq_nonneg _) (hV0 y))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← hQn n]
    exact (hS (φ n)).2.trans (mul_le_mul_of_nonneg_left (h2sum (φ n)) (by norm_num))
  have hmeasF : AEStronglyMeasurable (fun y => ‖x y‖ ^ 2 * V y) volume :=
    ((Lp.aestronglyMeasurable x).norm.pow 2).mul hVm.aestronglyMeasurable
  have hmφ : ∀ i : ℕ, AEMeasurable (fun y => ENNReal.ofReal (‖φ (ns i) y‖ ^ 2 * V y)) volume :=
    fun i => ((((φ (ns i)).continuous.norm.pow 2).measurable.mul hVm).ennreal_ofReal).aemeasurable
  have hlint : ∫⁻ y, ENNReal.ofReal (‖x y‖ ^ 2 * V y) ≤
      ENNReal.ofReal (4 * (⟪U x, hdom.toLp _⟫_ℂ).re) := by
    calc ∫⁻ y, ENNReal.ofReal (‖x y‖ ^ 2 * V y)
        = ∫⁻ y, liminf (fun i => ENNReal.ofReal (‖φ (ns i) y‖ ^ 2 * V y)) atTop :=
          lintegral_congr_ae (by filter_upwards [hlim] with y hy; exact hy.liminf_eq.symm)
      _ ≤ liminf (fun i => ∫⁻ y, ENNReal.ofReal (‖φ (ns i) y‖ ^ 2 * V y)) atTop :=
          lintegral_liminf_le' hmφ
      _ ≤ liminf (fun i => ENNReal.ofReal (4 * (⟪(g (ns i)).toLp 2
            (volume : Measure (EuclideanSpace ℝ ι)), (hg (ns i)).toLp _⟫_ℂ).re)) atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall fun i => hFn (ns i))
      _ = ENNReal.ofReal (4 * (⟪U x, hdom.toLp _⟫_ℂ).re) := by
          refine Tendsto.liminf_eq ?_
          exact (ENNReal.continuous_ofReal.tendsto _).comp
            ((hQre.comp hns.tendsto_atTop).const_mul 4)
  have hint : Integrable (fun y => ‖x y‖ ^ 2 * V y) volume := by
    refine ⟨hmeasF, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hmeasF]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlint

end HVZDens


/-! C1 (bounded below) for 7ab9d8bf, reduced to the Hardy inequality in each electron coordinate. -/


open MeasureTheory TeschlQM.Shared TeschlQM.Atomic
open scoped InnerProductSpace ComplexConjugate

namespace HVZC1

/-- Hardy's inequality in the electron coordinate `x_j` (Fourier/form version):
`∫ |ψ|²/|x_j|² ≤ 4 ⟨ψ, H₀ ψ⟩` for `ψ ∈ 𝔇(H₀) = H²(ℝ^{3N})`. -/
def HardyElectron : Prop :=
  ∀ (N : ℕ) (j : Fin N)
    (ψ : (freeHamiltonian (Fin N × Fin 3)).domain),
    Integrable (fun x => ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) x‖ ^ 2 /
        ‖electron x j‖ ^ 2) ∧
      ∫ x, ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) x‖ ^ 2 /
          ‖electron x j‖ ^ 2 ≤
        4 * (⟪(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))),
          freeHamiltonian (Fin N × Fin 3) ψ⟫_ℂ).re

/-- `H₀ ≥ 0`. -/
theorem freeHamiltonian_nonneg (ι : Type*) [Fintype ι]
    (ψ : (freeHamiltonian ι).domain) :
    0 ≤ (⟪(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))), freeHamiltonian ι ψ⟫_ℂ).re := by
  set U := Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ
  obtain ⟨x, hx⟩ := ψ
  have hdom : MemLp (fun ξ : EuclideanSpace ℝ ι =>
      ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * (U x : EuclideanSpace ℝ ι → ℂ) ξ) 2 volume :=
    Submodule.mem_comap.1 hx
  have hval : freeHamiltonian ι ⟨x, hx⟩ = U.symm (hdom.toLp _) := rfl
  rw [hval]
  show 0 ≤ (⟪x, U.symm (hdom.toLp _)⟫_ℂ).re
  rw [← U.inner_map_map, LinearIsometryEquiv.apply_symm_apply, L2.inner_def]
  have hre := integral_re (𝕜 := ℂ) (L2.integrable_inner (U x) (hdom.toLp _))
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hdom.coeFn_toLp] with ξ hξ
  rw [hξ, RCLike.inner_apply', Pi.zero_apply]
  have : (starRingEnd ℂ) ((U x : EuclideanSpace ℝ ι → ℂ) ξ) *
      (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * (U x : EuclideanSpace ℝ ι → ℂ) ξ) =
      ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖(U x : EuclideanSpace ℝ ι → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_left_comm, Complex.conj_mul']; push_cast; ring
  rw [this, Complex.ofReal_re]
  positivity

/-- Pointwise: `V^{(N)} ≥ -∑ γne/|x_j|` and AM-GM `1/r ≤ t/(2r²) + 1/(2t)`. -/
lemma pot_lower (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) (N : ℕ) (t : ℝ) (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin N × Fin 3)) (a : ℝ) (ha : 0 ≤ a) :
    -(∑ j : Fin N, γne * (t / 2 * (a / ‖electron x j‖ ^ 2) + 1 / (2 * t) * a)) ≤
      atomicPotential γne γee N x * a := by
  unfold atomicPotential
  have hee' : 0 ≤ ∑ j : Fin N, ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
      γee / ‖electron x j - electron x k‖ :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => div_nonneg hee.le (norm_nonneg _)
  have hr0 : ∀ r : ℝ, 0 ≤ r → γne / r * a ≤ γne * (t / 2 * (a / r ^ 2) + 1 / (2 * t) * a) := by
    intro r hr
    rcases hr.eq_or_lt with h0 | hr
    · rw [← h0]; simp only [div_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      positivity
    · have e : γne * (t / 2 * (a / r ^ 2) + 1 / (2 * t) * a) - γne / r * a =
          γne * a * (t - r) ^ 2 / (2 * t * r ^ 2) := by
        field_simp; ring
      have : 0 ≤ γne * a * (t - r) ^ 2 / (2 * t * r ^ 2) := by positivity
      linarith
  have hj : ∀ j : Fin N, γne / ‖electron x j‖ * a ≤
      γne * (t / 2 * (a / ‖electron x j‖ ^ 2) + 1 / (2 * t) * a) :=
    fun j => hr0 _ (norm_nonneg _)
  have hs : (∑ j : Fin N, γne / ‖electron x j‖) * a ≤
      ∑ j : Fin N, γne * (t / 2 * (a / ‖electron x j‖ ^ 2) + 1 / (2 * t) * a) := by
    rw [Finset.sum_mul]; exact Finset.sum_le_sum fun j _ => hj j
  nlinarith [mul_nonneg hee' ha]

end HVZC1

set_option maxHeartbeats 1000000 in
open HVZC1 in
/-- C1 from Hardy. -/
theorem c1_of_hardy (hardy : HardyElectron) (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee)
    (N : ℕ) : ∃ γ : ℝ, IsBoundedBelowBy (atomicHamiltonian γne γee N) γ := by
  refine ⟨-((N : ℝ) * (N + 1) * γne ^ 2), ?_⟩
  obtain ⟨H0, hH0⟩ : ∃ H0, H0 = freeHamiltonian (Fin N × Fin 3) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : EuclideanSpace ℝ (Fin N × Fin 3) → ℂ,
    g = fun x => ((atomicPotential γne γee N x : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨B, hB0⟩ : ∃ B, B = mulOp volume g := ⟨_, rfl⟩
  have hAH : atomicHamiltonian γne γee N = H0 + B := by rw [hH0, hB0, hg]; rfl
  rewrite [hAH]
  intro ψ
  obtain ⟨φ, hφ⟩ := ψ
  have hA : φ ∈ H0.domain := hφ.1
  have hB : φ ∈ B.domain := hφ.2
  have happ : (H0 + B) ⟨φ, hφ⟩ = H0 ⟨φ, hA⟩ + B ⟨φ, hB⟩ := LinearPMap.add_apply H0 B ⟨φ, hφ⟩
  have hBm : MemLp (fun x => g x * (φ : _ → ℂ) x) 2 volume := by subst hB0; exact hB
  have hBval : B ⟨φ, hB⟩ = hBm.toLp _ := by subst hB0; rfl
  set t : ℝ := 1 / (2 * (N + 1) * γne) with ht_def
  have ht : 0 < t := by positivity
  let a : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ := fun x => ‖(φ : _ → ℂ) x‖ ^ 2
  have hai : Integrable a := (Lp.memLp φ).norm.integrable_sq
  have hhar := fun j : Fin N => (by subst hH0; exact hardy N j ⟨φ, hA⟩ :
    Integrable (fun x => ‖(φ : _ → ℂ) x‖ ^ 2 / ‖electron x j‖ ^ 2) ∧
      ∫ x, ‖(φ : _ → ℂ) x‖ ^ 2 / ‖electron x j‖ ^ 2 ≤ 4 * (⟪φ, H0 ⟨φ, hA⟩⟫_ℂ).re)
  set q := (⟪φ, H0 ⟨φ, hA⟩⟫_ℂ).re
  have hq : 0 ≤ q := by subst hH0; exact freeHamiltonian_nonneg _ ⟨φ, hA⟩
  have hnorm : ‖φ‖ ^ 2 = ∫ x, a x := by
    rewrite [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [a, inner_self_eq_norm_sq_to_K]; norm_cast
  let L : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ := fun x =>
    -(∑ j : Fin N, γne * (t / 2 * (a x / ‖electron x j‖ ^ 2) + 1 / (2 * t) * a x))
  have hLi : Integrable L := by
    refine (integrable_finsetSum _ fun j _ => ?_).neg
    exact (((hhar j).1.const_mul (t / 2)).add (hai.const_mul (1 / (2 * t)))).const_mul γne
  have hLint : ∫ x, L x = -(∑ j : Fin N, γne * (t / 2 *
      (∫ x, a x / ‖electron x j‖ ^ 2) + 1 / (2 * t) * ∫ x, a x)) := by
    simp only [L]
    have hij : ∀ j ∈ (Finset.univ : Finset (Fin N)), Integrable (fun x =>
        γne * (t / 2 * (a x / ‖electron x j‖ ^ 2) + 1 / (2 * t) * a x)) := fun j _ => by
      exact (((hhar j).1.const_mul (t / 2)).add (hai.const_mul (1 / (2 * t)))).const_mul γne
    rw [integral_neg, integral_finsetSum _ hij]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : Integrable (fun x => t / 2 * (a x / ‖electron x j‖ ^ 2)) := by
      exact (hhar j).1.const_mul _
    rw [integral_const_mul, integral_add h1 (hai.const_mul _),
      integral_const_mul, integral_const_mul]
  have hVlow : ∫ x, L x ≤ (⟪φ, B ⟨φ, hB⟩⟫_ℂ).re := by
    rw [L2.inner_def]
    have hre := integral_re (𝕜 := ℂ) (L2.integrable_inner φ (B ⟨φ, hB⟩))
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    have hire : Integrable (fun x => (⟪(φ : _ → ℂ) x, (B ⟨φ, hB⟩ : _ → ℂ) x⟫_ℂ).re) volume :=
      (L2.integrable_inner (𝕜 := ℂ) φ (B ⟨φ, hB⟩)).re
    refine integral_mono_ae hLi hire ?_
    rw [hBval]
    filter_upwards [hBm.coeFn_toLp] with x hx
    rw [hx, RCLike.inner_apply']
    have : (starRingEnd ℂ) ((φ : _ → ℂ) x) * (g x * (φ : _ → ℂ) x) =
        ((atomicPotential γne γee N x * a x : ℝ) : ℂ) := by
      simp only [hg, a]
      rw [mul_left_comm, Complex.conj_mul']; push_cast; ring
    rw [this, Complex.ofReal_re]
    exact pot_lower γne γee hne hee N t ht x (a x) (by positivity)
  have hsum : ∑ j : Fin N, γne * (t / 2 * (∫ x, a x / ‖electron x j‖ ^ 2) + 1 / (2 * t) * ∫ x, a x)
      ≤ ∑ j : Fin N, γne * (t / 2 * (4 * q) + 1 / (2 * t) * ∫ x, a x) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have := (hhar j).2
    gcongr
  have hsum' : ∑ j : Fin N, γne * (t / 2 * (4 * q) + 1 / (2 * t) * ∫ x, a x) =
      (N : ℝ) / (N + 1) * q + (N : ℝ) * (N + 1) * γne ^ 2 * ∫ x, a x := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ht_def]
    field_simp
    ring
  have htot : (⟪φ, (H0 + B) ⟨φ, hφ⟩⟫_ℂ).re =
      q + (⟪φ, B ⟨φ, hB⟩⟫_ℂ).re := by
    rw [happ, inner_add_right, Complex.add_re]
  show -((N : ℝ) * (N + 1) * γne ^ 2) * ‖φ‖ ^ 2 ≤ _
  rewrite [htot, hnorm]
  have hfrac : (N : ℝ) / (N + 1) * q ≤ q := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  linarith

open MeasureTheory SchwartzMap TeschlQM.Atomic in
theorem HVZC1.hardyElectron_holds : HVZC1.HardyElectron := by
  intro N j ψ
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin N × Fin 3) => (‖electron x j‖ ^ 2)⁻¹) := by
    unfold electron; fun_prop
  obtain ⟨h1, h2⟩ := HVZDens.hardy_ext _ hm (fun x => by positivity) (fun φ => by
    have h := HVZHardy.hardy_electron j φ
    simp only [div_eq_mul_inv] at h
    exact h) ψ
  simp only [div_eq_mul_inv]
  exact ⟨h1, h2⟩

open TeschlQM.Atomic in
theorem solution (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) (N : ℕ) :
    ∃ γ : ℝ, TeschlQM.Shared.IsBoundedBelowBy (atomicHamiltonian γne γee N) γ := by
  exact c1_of_hardy HVZC1.hardyElectron_holds γne γee hne hee N

-- Prove2me | solution 1 for TeschlQM.Atomic.atomicHamiltonian_symm_resolvent_formBound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T09:46:47.549532+00:00
-- url     : https://prove2.me/submissions/d0499717-f60a-4d3a-83a5-892175164d28

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian

/-! Grandchild D0 of 7ab9d8bf (HVZ), child of the essential-spectrum identity: H^N is symmetric,
has a real resolvent point, is bounded below, and controls the kinetic form.
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


/-- Hardy in the relative coordinate `x_j - x_k` of two electrons (translate the `x_j`-slice). -/
theorem hardy_pair (k : Fin N) (hkj : k ≠ j) (φ : 𝓢(EuclideanSpace ℝ (Fin N × Fin 3), ℂ)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin N × Fin 3) =>
      ‖φ x‖ ^ 2 / ‖(WithLp.toLp 2 (fun a => x (j, a)) : EuclideanSpace ℝ (Fin 3)) -
        WithLp.toLp 2 (fun a => x (k, a))‖ ^ 2) ∧
    ∫ x : EuclideanSpace ℝ (Fin N × Fin 3),
      ‖φ x‖ ^ 2 / ‖(WithLp.toLp 2 (fun a => x (j, a)) : EuclideanSpace ℝ (Fin 3)) -
        WithLp.toLp 2 (fun a => x (k, a))‖ ^ 2 ≤
      4 * ∫ x, ‖fderiv ℝ (⇑φ) x‖ ^ 2 := by
  have hV : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  let F : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ := fun x =>
    ‖φ x‖ ^ 2 / ‖(WithLp.toLp 2 (fun a => x (j, a)) : EuclideanSpace ℝ (Fin 3)) -
        WithLp.toLp 2 (fun a => x (k, a))‖ ^ 2
  let D : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ := fun x => ‖fderiv ℝ (⇑φ) x‖ ^ 2
  have hmp := insE_mp j
  let av : (Kj j → ℝ) → EuclideanSpace ℝ (Fin 3) := fun w =>
    WithLp.toLp 2 (fun b => w ⟨(k, b), hkj⟩)
  have hel : ∀ w y, (WithLp.toLp 2 (fun a => (ins j w y) (j, a)) : EuclideanSpace ℝ (Fin 3)) = y := by
    intro w y; ext a; simp [ins]
  have helk : ∀ w y, (WithLp.toLp 2 (fun a => (ins j w y) (k, a)) : EuclideanSpace ℝ (Fin 3)) = av w := by
    intro w y; ext a; simp [ins, av, hkj]
  have hFslice : ∀ w y, F (insE j (w, y)) = ‖φ (ins j w 0 + insL j y)‖ ^ 2 / ‖y - av w‖ ^ 2 := by
    intro w y; simp only [F, insE_apply, hel, helk, insL_apply, ← ins_split]
  have hDslice : ∀ w y, D (insE j (w, y)) = ‖fderiv ℝ (⇑φ) (ins j w 0 + insL j y)‖ ^ 2 := by
    intro w y; simp only [D, insE_apply, insL_apply, ← ins_split]
  have hS : ∀ w, Integrable (fun y => F (insE j (w, y))) ∧
      ∫ y, F (insE j (w, y)) ≤ 4 * ∫ y, D (insE j (w, y)) := by
    intro w
    have hsl := hardy_slice hV φ (insL j) (norm_insL j) (ins j w 0 + insL j (av w))
    have hc : ∀ y, ins j w 0 + insL j (av w) + insL j (y - av w) = ins j w 0 + insL j y := by
      intro y; rw [map_sub]; abel
    have e1 : (fun y => F (insE j (w, y))) = fun y =>
        (fun y' => ‖φ (ins j w 0 + insL j (av w) + insL j y')‖ ^ 2 / ‖y'‖ ^ 2) (y - av w) := by
      funext y; rw [hFslice]; exact congrArg (fun p => ‖φ p‖ ^ 2 / ‖y - av w‖ ^ 2) (hc y).symm
    have e2 : (fun y => D (insE j (w, y))) = fun y =>
        (fun y' => ‖fderiv ℝ (⇑φ) (ins j w 0 + insL j (av w) + insL j y')‖ ^ 2) (y - av w) := by
      funext y; rw [hDslice]; exact congrArg (fun p => ‖fderiv ℝ (⇑φ) p‖ ^ 2) (hc y).symm
    refine ⟨e1 ▸ hsl.1.comp_sub_right (av w), ?_⟩
    have i1 := integral_sub_right_eq_self (μ := volume)
      (fun y' => ‖φ (ins j w 0 + insL j (av w) + insL j y')‖ ^ 2 / ‖y'‖ ^ 2) (av w)
    have i2 := integral_sub_right_eq_self (μ := volume)
      (fun y' => ‖fderiv ℝ (⇑φ) (ins j w 0 + insL j (av w) + insL j y')‖ ^ 2) (av w)
    rw [e1, e2]
    calc _ = _ := i1
      _ ≤ _ := hsl.2.2
      _ = _ := (congrArg (fun t => 4 * t) i2).symm
  have hF0 : ∀ x, 0 ≤ F x := fun x => by positivity
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
  have hGP : Integrable (F ∘ insE j) (volume.prod volume) := by
    refine (integrable_prod_iff hGm).2 ⟨Filter.Eventually.of_forall fun w => (hS w).1, ?_⟩
    refine (hDP.integral_prod_left.const_mul 4).mono' hGm.norm.integral_prod_right'
      (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    simp only [Function.comp_apply, Real.norm_of_nonneg (hF0 _)]
    exact (hS w).2
  refine ⟨(hmp.integrable_comp_emb (insE j).measurableEmbedding).1 hGP, ?_⟩
  rw [← hmp.integral_comp' (g := F), ← hmp.integral_comp' (g := D)]
  change ∫ q, (F ∘ insE j) q ∂(volume.prod volume) ≤ 4 * ∫ q, (D ∘ insE j) q ∂(volume.prod volume)
  rw [integral_prod _ hGP, integral_prod _ hDP, ← integral_const_mul]
  exact integral_mono hGP.integral_prod_left (hDP.integral_prod_left.const_mul 4) fun w => (hS w).2

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





set_option autoImplicit false

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace HVZC2

theorem nontrivial_L2 (M : ℕ) :
    Nontrivial (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3)))) := by
  have hs : MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin M × Fin 3)) 1) :=
    measurableSet_ball
  have hμ : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin M × Fin 3)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  refine nontrivial_of_ne (indicatorConstLp 2 hs hμ (1 : ℂ)) 0 ?_
  intro h
  have hn := norm_indicatorConstLp (p := 2) (by norm_num) (by norm_num) (hs := hs) (hμs := hμ) (c := (1 : ℂ))
  rw [h, norm_zero, norm_one, one_mul] at hn
  have hpos : 0 < volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin M × Fin 3)) 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' hμ
  have : 0 < volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin M × Fin 3)) 1) ^ (1 / (2 : ENNReal).toReal) :=
    Real.rpow_pos_of_pos hpos _
  linarith

theorem mulOp_symm {X : Type*} [MeasurableSpace X] (μ : Measure X) (V : X → ℝ)
    (φ ψ : (TeschlQM.Atomic.mulOp μ (fun x => ((V x : ℝ) : ℂ))).domain) :
    ⟪TeschlQM.Atomic.mulOp μ (fun x => ((V x : ℝ) : ℂ)) φ, (ψ : Lp ℂ 2 μ)⟫_ℂ =
      ⟪(φ : Lp ℂ 2 μ), TeschlQM.Atomic.mulOp μ (fun x => ((V x : ℝ) : ℂ)) ψ⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  have h1 := MemLp.coeFn_toLp φ.2
  have h2 := MemLp.coeFn_toLp ψ.2
  filter_upwards [h1, h2] with x hx1 hx2
  change ⟪(MemLp.toLp _ φ.2 : Lp ℂ 2 μ) x, (ψ : Lp ℂ 2 μ) x⟫_ℂ =
    ⟪(φ : Lp ℂ 2 μ) x, (MemLp.toLp _ ψ.2 : Lp ℂ 2 μ) x⟫_ℂ
  rw [hx1, hx2]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem free_symm (ι : Type*) [Fintype ι]
    (φ ψ : (TeschlQM.Atomic.freeHamiltonian ι).domain) :
    ⟪TeschlQM.Atomic.freeHamiltonian ι φ, (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))⟫_ℂ =
      ⟪(φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))), TeschlQM.Atomic.freeHamiltonian ι ψ⟫_ℂ := by
  let F := Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ
  let g := fun ξ : EuclideanSpace ℝ ι => (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ)
  have hφ : F φ ∈ (TeschlQM.Atomic.mulOp volume g).domain := φ.2
  have hψ : F ψ ∈ (TeschlQM.Atomic.mulOp volume g).domain := ψ.2
  have e1 : TeschlQM.Atomic.freeHamiltonian ι φ = F.symm (TeschlQM.Atomic.mulOp volume g ⟨F φ, hφ⟩) := rfl
  have e2 : TeschlQM.Atomic.freeHamiltonian ι ψ = F.symm (TeschlQM.Atomic.mulOp volume g ⟨F ψ, hψ⟩) := rfl
  rw [e1, e2, ← F.inner_map_map (F.symm _) (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))),
    F.apply_symm_apply, ← F.inner_map_map (φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) (F.symm _),
    F.apply_symm_apply]
  exact mulOp_symm volume (fun ξ => 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ⟨F φ, hφ⟩ ⟨F ψ, hψ⟩

set_option maxHeartbeats 400000 in
theorem atomic_symm (γne γee : ℝ) (M : ℕ)
    (φ ψ : (TeschlQM.Atomic.atomicHamiltonian γne γee M).domain) :
    ⟪TeschlQM.Atomic.atomicHamiltonian γne γee M φ,
        (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3))))⟫_ℂ =
      ⟪(φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3)))),
        TeschlQM.Atomic.atomicHamiltonian γne γee M ψ⟫_ℂ := by
  have e1 : TeschlQM.Atomic.atomicHamiltonian γne γee M φ =
      TeschlQM.Atomic.freeHamiltonian (Fin M × Fin 3) ⟨φ, φ.2.1⟩ +
        TeschlQM.Atomic.mulOp volume
          (fun x => ((TeschlQM.Atomic.atomicPotential γne γee M x : ℝ) : ℂ)) ⟨φ, φ.2.2⟩ :=
    LinearPMap.add_apply _ _ φ
  have e2 : TeschlQM.Atomic.atomicHamiltonian γne γee M ψ =
      TeschlQM.Atomic.freeHamiltonian (Fin M × Fin 3) ⟨ψ, ψ.2.1⟩ +
        TeschlQM.Atomic.mulOp volume
          (fun x => ((TeschlQM.Atomic.atomicPotential γne γee M x : ℝ) : ℂ)) ⟨ψ, ψ.2.2⟩ :=
    LinearPMap.add_apply _ _ ψ
  have h1 := free_symm (Fin M × Fin 3) ⟨φ, φ.2.1⟩ ⟨ψ, ψ.2.1⟩
  have h2 := mulOp_symm (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3)))
    (fun x => TeschlQM.Atomic.atomicPotential γne γee M x) ⟨φ, φ.2.2⟩ ⟨ψ, ψ.2.2⟩
  rw [e1, e2, inner_add_left, inner_add_right]
  exact congrArg₂ (· + ·) h1 h2

end HVZC2


set_option autoImplicit false

open TeschlQM.Atomic

namespace HVZPot

theorem pot_sq_le (γne γee : ℝ) (N : ℕ) (x : EuclideanSpace ℝ (Fin N × Fin 3)) :
    atomicPotential γne γee N x ^ 2 ≤
      2 * N * γne ^ 2 * ∑ j : Fin N, (‖electron x j‖ ^ 2)⁻¹ +
        2 * N ^ 2 * γee ^ 2 * ∑ j : Fin N, ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
          (‖electron x j - electron x k‖ ^ 2)⁻¹ := by
  unfold atomicPotential
  have key : ∀ γ r : ℝ, (γ / r) ^ 2 = γ ^ 2 * (r ^ 2)⁻¹ := fun γ r => by
    rw [div_pow, div_eq_mul_inv]
  have ha : (∑ j : Fin N, γne / ‖electron x j‖) ^ 2 ≤
      N * (γne ^ 2 * ∑ j : Fin N, (‖electron x j‖ ^ 2)⁻¹) := by
    refine sq_sum_le_card_mul_sum_sq.trans (le_of_eq ?_)
    simp only [Finset.card_univ, Fintype.card_fin, key, Finset.mul_sum]
  have hin : ∀ j : Fin N,
      (∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k), γee / ‖electron x j - electron x k‖) ^ 2 ≤
        N * (γee ^ 2 * ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
          (‖electron x j - electron x k‖ ^ 2)⁻¹) := by
    intro j
    refine sq_sum_le_card_mul_sum_sq.trans ?_
    simp only [key, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have := Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun k : Fin N => j < k)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have hb : (∑ j : Fin N, ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
        γee / ‖electron x j - electron x k‖) ^ 2 ≤
      N * ∑ j : Fin N, (N * (γee ^ 2 * ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
          (‖electron x j - electron x k‖ ^ 2)⁻¹)) := by
    refine sq_sum_le_card_mul_sum_sq.trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    gcongr with j
    exact hin j
  have e : (N : ℝ) * ∑ j : Fin N, (N * (γee ^ 2 * ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
          (‖electron x j - electron x k‖ ^ 2)⁻¹)) =
      N ^ 2 * γee ^ 2 * ∑ j : Fin N, ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
          (‖electron x j - electron x k‖ ^ 2)⁻¹ := by
    simp only [← Finset.mul_sum]; ring
  have hsq : ∀ a b : ℝ, (-a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := fun a b => by
    nlinarith [sq_nonneg (a + b)]
  refine (hsq _ _).trans ?_
  rw [e] at hb
  linarith

end HVZPot


set_option autoImplicit false

open MeasureTheory
open scoped InnerProductSpace

namespace HVZR0

abbrev E (ι : Type*) := EuclideanSpace ℝ ι
noncomputable abbrev L2 (ι : Type*) [Fintype ι] := Lp ℂ 2 (volume : Measure (E ι))
noncomputable abbrev U (ι : Type*) [Fintype ι] : L2 ι ≃ₗᵢ[ℂ] L2 ι := Lp.fourierTransformₗᵢ (E ι) ℂ

variable {ι : Type*} [Fintype ι]

noncomputable def sym (ξ : E ι) : ℂ := ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)

theorem sym_cont : Continuous (sym (ι := ι)) := by unfold sym; fun_prop

theorem mem_dom (ψ : L2 ι) :
    ψ ∈ (TeschlQM.Atomic.freeHamiltonian ι).domain ↔
      MemLp (fun ξ => sym ξ * (U ι ψ : E ι → ℂ) ξ) 2 volume := Iff.rfl

theorem U_H0 (x : L2 ι) (h : x ∈ (TeschlQM.Atomic.freeHamiltonian ι).domain) :
    (U ι (TeschlQM.Atomic.freeHamiltonian ι ⟨x, h⟩) : E ι → ℂ) =ᵐ[volume]
      fun ξ => sym ξ * (U ι x : E ι → ℂ) ξ := by
  have hval : TeschlQM.Atomic.freeHamiltonian ι ⟨x, h⟩ = (U ι).symm (((mem_dom x).1 h).toLp _) := rfl
  rw [hval, LinearIsometryEquiv.apply_symm_apply]
  exact MemLp.coeFn_toLp _

theorem memLp_mul (g : E ι → ℂ) (hg : Measurable g) (C : ℝ) (hC : ∀ ξ, ‖g ξ‖ ≤ C)
    (f : L2 ι) : MemLp (fun ξ => g ξ * (f : E ι → ℂ) ξ) 2 volume :=
  MemLp.of_le_mul (Lp.memLp f) (hg.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (ae_of_all _ fun ξ => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _))

noncomputable def mulCLM (g : E ι → ℂ) (hg : Measurable g) (C : ℝ)
    (hC : ∀ ξ, ‖g ξ‖ ≤ C) : L2 ι →L[ℂ] L2 ι :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_mul g hg C hC f).toLp _
      map_add' := by
        intro a b
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_add a b] with x hx
        simp only [Pi.add_apply, hx, mul_add]
      map_smul' := by
        intro c a
        rw [← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_smul c a] with x hx
        simp only [Pi.smul_apply, hx, smul_eq_mul, RingHom.id_apply]
        ring }
    C (by
      intro f
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(memLp_mul g hg C hC f).coeFn_toLp] with ξ hξ
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [hξ, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _))

theorem mulCLM_ae (g : E ι → ℂ) (hg : Measurable g) (C : ℝ) (hC : ∀ ξ, ‖g ξ‖ ≤ C)
    (f : L2 ι) : (mulCLM g hg C hC f : E ι → ℂ) =ᵐ[volume] fun ξ => g ξ * (f : E ι → ℂ) ξ :=
  (memLp_mul g hg C hC f).coeFn_toLp

/-! ## The free resolvent at `-t`, `t > 0` -/

noncomputable def mt (t : ℝ) (ξ : E ι) : ℂ := (sym ξ + t)⁻¹

theorem sym_add_ne {t : ℝ} (ht : 0 < t) (ξ : E ι) : sym ξ + (t : ℂ) ≠ 0 := by
  unfold sym; norm_cast; positivity

theorem mt_meas (t : ℝ) : Measurable (mt (ι := ι) t) :=
  (sym_cont.measurable.add_const _).inv

theorem mt_real (t : ℝ) (ξ : E ι) :
    mt t ξ = (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 + t)⁻¹ : ℝ) : ℂ) := by
  unfold mt sym; push_cast; ring

theorem mt_le {t : ℝ} (ht : 0 < t) (ξ : E ι) : ‖mt t ξ‖ ≤ 1 / t := by
  have hs : 0 ≤ 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
  rw [mt_real, Complex.norm_real, Real.norm_of_nonneg (by positivity), one_div]
  exact inv_anti₀ ht (by linarith)

theorem sym_mt_le {t : ℝ} (ht : 0 < t) (ξ : E ι) : ‖sym ξ * mt t ξ‖ ≤ 1 := by
  have hs : 0 ≤ 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have : sym ξ * mt t ξ =
      (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 + t)⁻¹ : ℝ) : ℂ) := by
    rw [mt_real]; unfold sym; push_cast; ring
  rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv,
    div_le_one (by positivity)]
  linarith

noncomputable def R0 {t : ℝ} (ht : 0 < t) : L2 ι →L[ℂ] L2 ι :=
  ((U ι).symm.toContinuousLinearEquiv : L2 ι →L[ℂ] L2 ι).comp
    ((mulCLM (mt t) (mt_meas t) _ (mt_le ht)).comp
      ((U ι).toContinuousLinearEquiv : L2 ι →L[ℂ] L2 ι))

theorem U_R0 {t : ℝ} (ht : 0 < t) (φ : L2 ι) :
    U ι (R0 ht φ) = mulCLM (mt t) (mt_meas t) _ (mt_le ht) (U ι φ) := by
  simp [R0]

theorem U_R0_ae {t : ℝ} (ht : 0 < t) (φ : L2 ι) :
    (U ι (R0 ht φ) : E ι → ℂ) =ᵐ[volume] fun ξ => mt t ξ * (U ι φ : E ι → ℂ) ξ := by
  rw [U_R0]; exact mulCLM_ae _ _ _ _ _

theorem R0_mem {t : ℝ} (ht : 0 < t) (φ : L2 ι) :
    R0 ht φ ∈ (TeschlQM.Atomic.freeHamiltonian ι).domain := by
  rw [mem_dom]
  refine MemLp.of_le_mul (c := 1) (Lp.memLp (U ι φ))
    ((sym_cont.measurable.aestronglyMeasurable).mul (Lp.aestronglyMeasurable _)) ?_
  filter_upwards [U_R0_ae ht φ] with ξ hξ
  rw [hξ, ← mul_assoc, norm_mul]
  exact mul_le_mul_of_nonneg_right (sym_mt_le ht ξ) (norm_nonneg _)

theorem isResolvent_R0 {t : ℝ} (ht : 0 < t) :
    TeschlQM.Shared.IsResolventAt (TeschlQM.Atomic.freeHamiltonian ι) (-(t : ℂ)) (R0 ht) := by
  constructor
  · intro φ
    have hmem := R0_mem ht φ
    refine ⟨hmem, ?_⟩
    apply (U ι).injective
    apply Lp.ext
    rw [map_sub, map_smul]
    filter_upwards [Lp.coeFn_sub (U ι (TeschlQM.Atomic.freeHamiltonian ι ⟨_, hmem⟩))
      ((-(t : ℂ)) • U ι (R0 ht φ)), Lp.coeFn_smul (-(t : ℂ)) (U ι (R0 ht φ)), U_H0 _ hmem,
      U_R0_ae ht φ] with ξ h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, smul_eq_mul, h4, ← sub_mul, sub_neg_eq_add, mt,
      ← mul_assoc, mul_inv_cancel₀ (sym_add_ne ht ξ), one_mul]
  · rintro ⟨x, hx⟩
    apply (U ι).injective
    apply Lp.ext
    filter_upwards [U_R0_ae ht (TeschlQM.Atomic.freeHamiltonian ι ⟨x, hx⟩ - (-(t : ℂ)) • x),
      Lp.coeFn_sub (U ι (TeschlQM.Atomic.freeHamiltonian ι ⟨x, hx⟩)) ((-(t : ℂ)) • U ι x),
      Lp.coeFn_smul (-(t : ℂ)) (U ι x), U_H0 x hx] with ξ h1 h2 h3 h4
    rw [h1, map_sub, map_smul, h2, Pi.sub_apply, h3, Pi.smul_apply, h4, smul_eq_mul, ← sub_mul,
      sub_neg_eq_add, mt, ← mul_assoc, inv_mul_cancel₀ (sym_add_ne ht ξ), one_mul]

theorem norm_R0_le {t : ℝ} (ht : 0 < t) (φ : L2 ι) : ‖R0 ht φ‖ ≤ 1 / t * ‖φ‖ := by
  rw [← (U ι).norm_map (R0 ht φ), ← (U ι).norm_map φ]
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [U_R0_ae ht φ] with ξ hξ
  rw [hξ, norm_mul]
  exact mul_le_mul_of_nonneg_right (mt_le ht ξ) (norm_nonneg _)

theorem norm_H0_R0_le {t : ℝ} (ht : 0 < t) (φ : L2 ι) :
    ‖TeschlQM.Atomic.freeHamiltonian ι ⟨R0 ht φ, R0_mem ht φ⟩‖ ≤ ‖φ‖ := by
  rw [← (U ι).norm_map, ← (U ι).norm_map φ]
  refine (Lp.norm_le_mul_norm_of_ae_le_mul (c := 1) ?_).trans (by rw [one_mul])
  filter_upwards [U_H0 _ (R0_mem ht φ), U_R0_ae ht φ] with ξ h1 h2
  rw [h1, h2, ← mul_assoc, norm_mul]
  exact mul_le_mul_of_nonneg_right (sym_mt_le ht ξ) (norm_nonneg _)

theorem form_R0_le {t : ℝ} (ht : 0 < t) (φ : L2 ι) :
    (⟪(R0 ht φ : L2 ι), TeschlQM.Atomic.freeHamiltonian ι ⟨R0 ht φ, R0_mem ht φ⟩⟫_ℂ).re ≤
      1 / t * ‖φ‖ ^ 2 := by
  refine (re_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
  calc ‖R0 ht φ‖ * ‖TeschlQM.Atomic.freeHamiltonian ι ⟨R0 ht φ, R0_mem ht φ⟩‖
      ≤ (1 / t * ‖φ‖) * ‖φ‖ :=
        mul_le_mul (norm_R0_le ht φ) (norm_H0_R0_le ht φ) (norm_nonneg _) (by positivity)
    _ = 1 / t * ‖φ‖ ^ 2 := by ring

end HVZR0


set_option autoImplicit false

open TeschlQM.Shared

namespace HVZKR

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Abstract Kato–Rellich step: if `B R₀` is a bounded operator of norm `< 1`, then
`R₀ (1 + B R₀)⁻¹` is the resolvent of `A + B` at `z`. -/
theorem kato_rellich (A B : H →ₗ.[ℂ] H) (hdom : A.domain ≤ B.domain) (z : ℂ) (R0 : H →L[ℂ] H)
    (hR0 : IsResolventAt A z R0) (K : H →L[ℂ] H)
    (hK : ∀ φ : H, ∀ h : R0 φ ∈ B.domain, B ⟨R0 φ, h⟩ = K φ) (hKn : ‖K‖ < 1) :
    z ∈ resolventSet (A + B) := by
  let U : (H →L[ℂ] H)ˣ := Units.oneSub (-K) (by rwa [norm_neg])
  have hU : (U : H →L[ℂ] H) = 1 + K := by
    show (1 : H →L[ℂ] H) - (-K) = 1 + K
    rw [sub_neg_eq_add]
  refine ⟨R0.comp (↑U⁻¹ : H →L[ℂ] H), ?_, ?_⟩
  · intro φ
    set w := (↑U⁻¹ : H →L[ℂ] H) φ with hw
    obtain ⟨hA, hAeq⟩ := hR0.1 w
    have hB : R0 w ∈ B.domain := hdom hA
    have hUw : (U : H →L[ℂ] H) w = φ := by
      rw [hw, ← ContinuousLinearMap.mul_apply, Units.mul_inv, ContinuousLinearMap.one_apply]
    refine ⟨⟨hA, hB⟩, ?_⟩
    have hsum : (A + B) ⟨R0 w, ⟨hA, hB⟩⟩ = A ⟨R0 w, hA⟩ + B ⟨R0 w, hB⟩ :=
      LinearPMap.add_apply _ _ _
    show (A + B) ⟨R0 w, ⟨hA, hB⟩⟩ - z • R0 w = φ
    rw [hsum, hK w hB, ← hUw, hU, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
]
    rw [add_sub_right_comm, hAeq]
  · intro ψ
    have hψA : (ψ : H) ∈ A.domain := ψ.2.1
    have hψB : (ψ : H) ∈ B.domain := ψ.2.2
    set u := A ⟨ψ, hψA⟩ - z • (ψ : H) with hu
    have hRu : R0 u = ψ := hR0.2 ⟨ψ, hψA⟩
    have hRuB : R0 u ∈ B.domain := hRu ▸ hψB
    have hKu : K u = B ⟨ψ, hψB⟩ := by
      rw [← hK u hRuB]
      exact congrArg B (Subtype.ext hRu)
    have hsum : (A + B) ψ = A ⟨ψ, hψA⟩ + B ⟨ψ, hψB⟩ := LinearPMap.add_apply _ _ ψ
    have hUu : (A + B) ψ - z • (ψ : H) = (U : H →L[ℂ] H) u := by
      rw [hsum, hU, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply, hKu, hu]
      abel
    have hinv : (↑U⁻¹ : H →L[ℂ] H) ((U : H →L[ℂ] H) u) = u := by
      rw [← ContinuousLinearMap.mul_apply, Units.inv_mul, ContinuousLinearMap.one_apply]
    show R0 ((↑U⁻¹ : H →L[ℂ] H) ((A + B) ψ - z • (ψ : H))) = ψ
    rw [hUu, hinv, hRu]

end HVZKR


namespace HVZB
open MeasureTheory TeschlQM.Atomic TeschlQM.Shared
open scoped InnerProductSpace

def HE : Prop :=
  ∀ (N : ℕ) (j : Fin N) (ψ : (freeHamiltonian (Fin N × Fin 3)).domain),
    Integrable (fun x => ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) x‖ ^ 2 /
        ‖electron x j‖ ^ 2) ∧
      ∫ x, ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) x‖ ^ 2 /
          ‖electron x j‖ ^ 2 ≤
        4 * (⟪(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))),
          freeHamiltonian (Fin N × Fin 3) ψ⟫_ℂ).re

def HP : Prop :=
  ∀ (N : ℕ) (j k : Fin N), k ≠ j → ∀ (ψ : (freeHamiltonian (Fin N × Fin 3)).domain),
    Integrable (fun x => ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) x‖ ^ 2 /
        ‖electron x j - electron x k‖ ^ 2) ∧
      ∫ x, ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) x‖ ^ 2 /
          ‖electron x j - electron x k‖ ^ 2 ≤
        4 * (⟪(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))),
          freeHamiltonian (Fin N × Fin 3) ψ⟫_ℂ).re

def H0N : Prop :=
  ∀ (N : ℕ) (ψ : (freeHamiltonian (Fin N × Fin 3)).domain),
    0 ≤ (⟪(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))),
          freeHamiltonian (Fin N × Fin 3) ψ⟫_ℂ).re

theorem pot_meas (γne γee : ℝ) (N : ℕ) : Measurable (atomicPotential γne γee N) := by
  unfold atomicPotential electron
  refine (Finset.measurable_sum _ fun j _ => ?_).neg.add
    (Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_) <;> fun_prop

theorem norm_sq_L2 {N : ℕ} (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) :
    ‖f‖ ^ 2 = ∫ x, ‖(f : _ → ℂ) x‖ ^ 2 := by
  rewrite [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [inner_self_eq_norm_sq_to_K]; norm_cast

theorem vbound (hE : HE) (hP : HP) (h0 : H0N) (γne γee : ℝ) (N : ℕ)
    (ψ : (freeHamiltonian (Fin N × Fin 3)).domain) :
    ∃ h : (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) ∈
        (mulOp volume (fun x => ((atomicPotential γne γee N x : ℝ) : ℂ))).domain,
      ‖mulOp volume (fun x => ((atomicPotential γne γee N x : ℝ) : ℂ)) ⟨ψ, h⟩‖ ^ 2 ≤
        (8 * N ^ 2 * γne ^ 2 + 8 * N ^ 4 * γee ^ 2) *
          (⟪(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))),
            freeHamiltonian (Fin N × Fin 3) ψ⟫_ℂ).re := by
  have hq : 0 ≤ (⟪(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))),
            freeHamiltonian (Fin N × Fin 3) ψ⟫_ℂ).re := h0 N ψ
  set q := (⟪(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))),
            freeHamiltonian (Fin N × Fin 3) ψ⟫_ℂ).re with hq_def
  let g : EuclideanSpace ℝ (Fin N × Fin 3) → ℂ := fun x => ((atomicPotential γne γee N x : ℝ) : ℂ)
  let c : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ := fun x =>
    ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) x‖ ^ 2
  let G : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ := fun x =>
    2 * N * γne ^ 2 * ∑ j : Fin N, c x / ‖electron x j‖ ^ 2 +
      2 * N ^ 2 * γee ^ 2 * ∑ j : Fin N, ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
        c x / ‖electron x j - electron x k‖ ^ 2
  have hne : ∀ j k : Fin N, k ∈ Finset.univ.filter (fun k : Fin N => j < k) → k ≠ j :=
    fun j k hk => (ne_of_lt (Finset.mem_filter.1 hk).2).symm
  have hI1 : Integrable (fun x => ∑ j : Fin N, c x / ‖electron x j‖ ^ 2) :=
    integrable_finsetSum _ fun j _ => (hE N j ψ).1
  have hI2 : ∀ j : Fin N, Integrable (fun x => ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
      c x / ‖electron x j - electron x k‖ ^ 2) := fun j =>
    integrable_finsetSum _ fun k hk => (hP N j k (hne j k hk) ψ).1
  have hGi : Integrable G :=
    (hI1.const_mul _).add ((integrable_finsetSum _ fun j _ => hI2 j).const_mul _)
  have hpt : ∀ x, ‖g x * (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) x‖ ^ 2
      ≤ G x := by
    intro x
    have h1 := HVZPot.pot_sq_le γne γee N x
    have h2 : ‖g x * (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) x‖ ^ 2 =
        atomicPotential γne γee N x ^ 2 * c x := by
      simp only [g, c, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [h2]
    calc _ ≤ (2 * N * γne ^ 2 * ∑ j : Fin N, (‖electron x j‖ ^ 2)⁻¹ +
        2 * N ^ 2 * γee ^ 2 * ∑ j : Fin N, ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
          (‖electron x j - electron x k‖ ^ 2)⁻¹) * c x :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = G x := by
          simp only [G, add_mul, mul_assoc, Finset.sum_mul, div_eq_mul_inv, mul_comm (c x)]
  have hgm : Measurable g := Complex.measurable_ofReal.comp (pot_meas γne γee N)
  have hmeas : AEStronglyMeasurable
      (fun x => g x * (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) x) volume :=
    hgm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)
  have hmem : MemLp
      (fun x => g x * (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) x) 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm hmeas]
    refine hGi.mono' (hmeas.norm.pow 2) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt x
  refine ⟨hmem, ?_⟩
  have hval : ((mulOp volume g ⟨ψ, hmem⟩ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))
      : _ → ℂ) =ᵐ[volume]
      fun x => g x * (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) x :=
    MemLp.coeFn_toLp hmem
  have hint : ∫ x, G x = 2 * N * γne ^ 2 * ∑ j : Fin N, (∫ x, c x / ‖electron x j‖ ^ 2) +
      2 * N ^ 2 * γee ^ 2 * ∑ j : Fin N, ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
        (∫ x, c x / ‖electron x j - electron x k‖ ^ 2) := by
    simp only [G]
    rw [integral_add (hI1.const_mul _) ((integrable_finsetSum _ fun j _ => hI2 j).const_mul _),
      integral_const_mul, integral_const_mul, integral_finsetSum _ (fun j _ => (hE N j ψ).1),
      integral_finsetSum _ (fun j _ => hI2 j)]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun j _ =>
      integral_finsetSum _ fun k hk => (hP N j k (hne j k hk) ψ).1
  have hin : ∑ j : Fin N, ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k), 4 * q ≤
      N * (N * (4 * q)) := by
    calc _ ≤ ∑ j : Fin N, ∑ k : Fin N, 4 * q := Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by linarith)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [norm_sq_L2]
  calc _ = ∫ x, ‖g x * (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) x‖ ^ 2 :=
        integral_congr_ae (hval.mono fun x hx => by beta_reduce; rw [hx])
    _ ≤ ∫ x, G x := integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hGi
        (Filter.Eventually.of_forall hpt)
    _ ≤ 2 * N * γne ^ 2 * ∑ j : Fin N, 4 * q + 2 * N ^ 2 * γee ^ 2 *
          ∑ j : Fin N, ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k), 4 * q := by
        rw [hint]
        gcongr
        · exact (hE N _ ψ).2
        · exact (hP N _ _ (hne _ _ (by assumption)) ψ).2
    _ ≤ _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h2 : (0 : ℝ) ≤ 2 * (N : ℝ) ^ 2 * γee ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hin h2]

theorem resolvent_pt (hE : HE) (hP : HP) (h0 : H0N) (γne γee : ℝ) (N : ℕ) (t : ℝ) (ht : 0 < t)
    (htK : 4 * (8 * N ^ 2 * γne ^ 2 + 8 * N ^ 4 * γee ^ 2) ≤ t) :
    -(t : ℂ) ∈ resolventSet (atomicHamiltonian γne γee N) := by
  have hK0 : (0 : ℝ) ≤ 8 * N ^ 2 * γne ^ 2 + 8 * N ^ 4 * γee ^ 2 := by positivity
  let B := mulOp volume
    (fun x : EuclideanSpace ℝ (Fin N × Fin 3) => ((atomicPotential γne γee N x : ℝ) : ℂ))
  let A := freeHamiltonian (Fin N × Fin 3)
  have hdom : A.domain ≤ B.domain := fun ψ hψ => by
    obtain ⟨h, -⟩ := vbound hE hP h0 γne γee N ⟨ψ, hψ⟩
    exact h
  let R0' : HVZR0.L2 (Fin N × Fin 3) →ₗ[ℂ] B.domain :=
    LinearMap.codRestrict B.domain (HVZR0.R0 ht).toLinearMap (fun φ => hdom (HVZR0.R0_mem ht φ))
  let Klin : HVZR0.L2 (Fin N × Fin 3) →ₗ[ℂ] HVZR0.L2 (Fin N × Fin 3) := B.toFun ∘ₗ R0'
  have hbound : ∀ φ, ‖Klin φ‖ ≤ 1 / 2 * ‖φ‖ := by
    intro φ
    obtain ⟨h, hle⟩ := vbound hE hP h0 γne γee N ⟨HVZR0.R0 ht φ, HVZR0.R0_mem ht φ⟩
    have heq : Klin φ = B ⟨HVZR0.R0 ht φ, h⟩ := rfl
    have hf := HVZR0.form_R0_le ht φ
    have hKt : (8 * N ^ 2 * γne ^ 2 + 8 * N ^ 4 * γee ^ 2) * (1 / t) ≤ (1 / 2) ^ 2 := by
      rw [mul_one_div, div_le_iff₀ ht]; linarith
    have hsq : ‖Klin φ‖ ^ 2 ≤ (1 / 2 * ‖φ‖) ^ 2 := by
      rw [heq]
      refine hle.trans (le_trans (mul_le_mul_of_nonneg_left hf hK0) ?_)
      calc (8 * N ^ 2 * γne ^ 2 + 8 * N ^ 4 * γee ^ 2) * (1 / t * ‖φ‖ ^ 2)
          = (8 * N ^ 2 * γne ^ 2 + 8 * N ^ 4 * γee ^ 2) * (1 / t) * ‖φ‖ ^ 2 := by ring
        _ ≤ (1 / 2) ^ 2 * ‖φ‖ ^ 2 := by gcongr
        _ = (1 / 2 * ‖φ‖) ^ 2 := by ring
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq
  let Kop : HVZR0.L2 (Fin N × Fin 3) →L[ℂ] HVZR0.L2 (Fin N × Fin 3) :=
    Klin.mkContinuous (1 / 2) hbound
  have hKn : ‖Kop‖ < 1 :=
    lt_of_le_of_lt (LinearMap.mkContinuous_norm_le Klin (by norm_num) hbound) (by norm_num)
  exact HVZKR.kato_rellich A B hdom (-(t : ℂ)) (HVZR0.R0 ht) (HVZR0.isResolvent_R0 ht) Kop
    (fun φ h => rfl) hKn

end HVZB


open MeasureTheory SchwartzMap TeschlQM.Atomic in
theorem HVZB.hardyPair_holds : HVZB.HP := by
  intro N j k hkj ψ
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin N × Fin 3) =>
      (‖electron x j - electron x k‖ ^ 2)⁻¹) := by
    unfold electron; fun_prop
  obtain ⟨h1, h2⟩ := HVZDens.hardy_ext _ hm (fun x => by positivity) (fun φ => by
    have h := HVZHardy.hardy_pair j k hkj φ
    simp only [div_eq_mul_inv] at h
    exact h) ψ
  simp only [div_eq_mul_inv]
  exact ⟨h1, h2⟩


set_option autoImplicit false

open MeasureTheory TeschlQM.Shared TeschlQM.Atomic HVZC1
open scoped InnerProductSpace ComplexConjugate

namespace HVZD0

set_option maxHeartbeats 1000000 in
/-- Kinetic form bound: `⟨φ,H₀φ⟩ ≤ 2⟨φ,Hφ⟩ + 4N(N+1)γ²‖φ‖²` (Hardy + Coulomb AM-GM). -/
theorem form_bound (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) (N : ℕ)
    (φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))
    (hA : φ ∈ (freeHamiltonian (Fin N × Fin 3)).domain)
    (hφ : φ ∈ (atomicHamiltonian γne γee N).domain) :
    (⟪φ, freeHamiltonian (Fin N × Fin 3) ⟨φ, hA⟩⟫_ℂ).re ≤
      2 * (⟪φ, atomicHamiltonian γne γee N ⟨φ, hφ⟩⟫_ℂ).re +
        4 * (N : ℝ) * (N + 1) * γne ^ 2 * ‖φ‖ ^ 2 := by
  have hardy := HVZC1.hardyElectron_holds
  obtain ⟨g, hg⟩ : ∃ g : EuclideanSpace ℝ (Fin N × Fin 3) → ℂ,
    g = fun x => ((atomicPotential γne γee N x : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨B, hB0⟩ : ∃ B, B = mulOp volume g := ⟨_, rfl⟩
  have hB : φ ∈ B.domain := by subst hB0 hg; exact hφ.2
  have happ : atomicHamiltonian γne γee N ⟨φ, hφ⟩ =
      freeHamiltonian (Fin N × Fin 3) ⟨φ, hA⟩ + B ⟨φ, hB⟩ := by
    subst hB0 hg
    exact LinearPMap.add_apply (freeHamiltonian (Fin N × Fin 3))
      (mulOp volume (fun x => ((atomicPotential γne γee N x : ℝ) : ℂ))) ⟨φ, hφ⟩
  revert hA happ
  generalize hH0 : freeHamiltonian (Fin N × Fin 3) = H0
  intro hA happ
  have hBm : MemLp (fun x => g x * (φ : _ → ℂ) x) 2 volume := by subst hB0; exact hB
  have hBval : B ⟨φ, hB⟩ = hBm.toLp _ := by subst hB0; rfl
  set t : ℝ := 1 / (4 * (N + 1) * γne) with ht_def
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
      (N : ℝ) / (2 * (N + 1)) * q + 2 * (N : ℝ) * (N + 1) * γne ^ 2 * ∫ x, a x := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ht_def]
    field_simp
    ring
  have htot : (⟪φ, atomicHamiltonian γne γee N ⟨φ, hφ⟩⟫_ℂ).re =
      q + (⟪φ, B ⟨φ, hB⟩⟫_ℂ).re := by
    rw [happ, inner_add_right, Complex.add_re]
  rewrite [htot, hnorm]
  have hfrac : (N : ℝ) / (2 * (N + 1)) * q ≤ q / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith

/-- A symmetric operator with a real resolvent point is densely defined. -/
theorem dense_of_resolvent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H)
    (hA : ∀ φ ψ : A.domain, ⟪(φ : H), A ψ⟫_ℂ = ⟪A φ, (ψ : H)⟫_ℂ) (t : ℝ)
    (ht : (t : ℂ) ∈ TeschlQM.Shared.resolventSet A) : Dense (A.domain : Set H) := by
  obtain ⟨R, hR1, -⟩ := ht
  have hperp : A.domainᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro ψ hψ
    obtain ⟨h1, e1⟩ := hR1 ψ
    have hφ0 : ∀ χ : H, ⟪R ψ, χ⟫_ℂ = 0 := by
      intro χ
      obtain ⟨h2, e2⟩ := hR1 χ
      have h0 : ⟪ψ, R χ⟫_ℂ = 0 := by
        rw [← inner_conj_symm, Submodule.inner_right_of_mem_orthogonal h2 hψ, map_zero]
      calc ⟪R ψ, χ⟫_ℂ = ⟪R ψ, A ⟨R χ, h2⟩ - (t : ℂ) • R χ⟫_ℂ := by rw [e2]
        _ = ⟪A ⟨R ψ, h1⟩, R χ⟫_ℂ - (t : ℂ) * ⟪R ψ, R χ⟫_ℂ := by
            rw [inner_sub_right, inner_smul_right]
            congr 1
            exact hA ⟨R ψ, h1⟩ ⟨R χ, h2⟩
        _ = ⟪ψ, R χ⟫_ℂ := by
            conv_rhs => rw [← e1]
            rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal]
        _ = 0 := h0
    have hR0 : R ψ = 0 := inner_self_eq_zero.mp (hφ0 _)
    have hz : (⟨R ψ, h1⟩ : A.domain) = 0 := Subtype.ext hR0
    rw [← e1, hz, LinearPMap.map_zero, hR0, smul_zero, sub_zero]
  rw [Submodule.dense_iff_topologicalClosure_eq_top, ← Submodule.orthogonal_orthogonal_eq_closure,
    hperp, Submodule.bot_orthogonal_eq_top]

end HVZD0

open TeschlQM.Atomic MeasureTheory Filter in
theorem solution (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) (N : ℕ) :
    TeschlQM.Shared.IsSymmetric (atomicHamiltonian γne γee N) ∧
    (∃ t : ℝ, (t : ℂ) ∈ TeschlQM.Shared.resolventSet (atomicHamiltonian γne γee N)) ∧
    (∃ γ : ℝ, TeschlQM.Shared.IsBoundedBelowBy (atomicHamiltonian γne γee N) γ) ∧
    ∃ C : ℝ, ∀ (ψ : (freeHamiltonian (Fin N × Fin 3)).domain)
      (hψ : (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) ∈ (atomicHamiltonian γne γee N).domain),
      (inner ℂ (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) (freeHamiltonian (Fin N × Fin 3) ψ)).re ≤
        2 * (inner ℂ (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) (atomicHamiltonian γne γee N ⟨ψ, hψ⟩)).re +
        C * ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ ^ 2 := by
  obtain ⟨γ, hγ⟩ := c1_of_hardy HVZC1.hardyElectron_holds γne γee hne hee N
  have hK0 : (0 : ℝ) ≤ 8 * N ^ 2 * γne ^ 2 + 8 * N ^ 4 * γee ^ 2 := by positivity
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = 4 * (8 * N ^ 2 * γne ^ 2 + 8 * N ^ 4 * γee ^ 2) + 1 :=
    ⟨_, rfl⟩
  have ht : 0 < t := by rw [ht_def]; positivity
  have hres := HVZB.resolvent_pt HVZC1.hardyElectron_holds HVZB.hardyPair_holds
    (fun N ψ => HVZC1.freeHamiltonian_nonneg _ ψ) γne γee N t ht (by linarith)
  have hres' : ((-t : ℝ) : ℂ) ∈ TeschlQM.Shared.resolventSet (atomicHamiltonian γne γee N) := by
    rw [Complex.ofReal_neg]; exact hres
  have hsym : ∀ φ ψ : (atomicHamiltonian γne γee N).domain,
      inner ℂ (φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))
        (atomicHamiltonian γne γee N ψ) =
      inner ℂ (atomicHamiltonian γne γee N φ)
        (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) :=
    fun φ ψ => (HVZC2.atomic_symm γne γee N φ ψ).symm
  refine ⟨⟨HVZD0.dense_of_resolvent _ hsym (-t) hres', hsym⟩, ⟨-t, hres'⟩, ⟨γ, hγ⟩,
    4 * (N : ℝ) * (N + 1) * γne ^ 2, fun ψ hψ => ?_⟩
  exact HVZD0.form_bound γne γee hne hee N ψ ψ.2 hψ

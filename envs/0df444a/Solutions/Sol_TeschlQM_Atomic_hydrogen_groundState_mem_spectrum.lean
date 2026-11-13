-- Prove2me | solution 1 for TeschlQM.Atomic.hydrogen_groundState_mem_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T10:47:48.671226+00:00
-- url     : https://prove2.me/submissions/ea05fcc7-2b03-44ac-90db-2699abd7f3d3

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian

/-! C4 step (1): one-dimensional Fourier transform of `e^{-a|t|}` and subordination. -/

set_option autoImplicit false

open MeasureTheory FourierTransform Complex Set

namespace HVZHyd

lemma exp_abs_Ioi (a w v : ℝ) (hv : 0 < v) :
    cexp (↑(-2 * Real.pi * v * w) * I) • ((Real.exp (-(a * |v|)) : ℝ) : ℂ) =
      cexp ((-(a : ℂ) - 2 * Real.pi * w * I) * v) := by
  rw [abs_of_pos hv, smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma exp_abs_Iic (a w v : ℝ) (hv : v ≤ 0) :
    cexp (↑(-2 * Real.pi * v * w) * I) • ((Real.exp (-(a * |v|)) : ℝ) : ℂ) =
      cexp (((a : ℂ) - 2 * Real.pi * w * I) * v) := by
  rw [abs_of_nonpos hv, smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `𝓕 (e^{-a|t|})(w) = 2a/(a² + 4π²w²)`. -/
theorem fourier_exp_neg_abs (a : ℝ) (ha : 0 < a) (w : ℝ) :
    𝓕 (fun t : ℝ => ((Real.exp (-(a * |t|)) : ℝ) : ℂ)) w =
      ((2 * a / (a ^ 2 + 4 * Real.pi ^ 2 * w ^ 2) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hR0 : ((-(a : ℂ) - 2 * Real.pi * w * I)).re < 0 := by simp [ha]
  have hL0 : 0 < (((a : ℂ) - 2 * Real.pi * w * I)).re := by simp [ha]
  have hRi : IntegrableOn (fun v : ℝ => cexp (↑(-2 * Real.pi * v * w) * I) •
      ((Real.exp (-(a * |v|)) : ℝ) : ℂ)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hR0 0).congr_fun
      (fun v hv => (exp_abs_Ioi a w v hv).symm) measurableSet_Ioi
  have hLi : IntegrableOn (fun v : ℝ => cexp (↑(-2 * Real.pi * v * w) * I) •
      ((Real.exp (-(a * |v|)) : ℝ) : ℂ)) (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic hL0 0).congr_fun
      (fun v hv => (exp_abs_Iic a w v hv).symm) measurableSet_Iic
  rw [← intervalIntegral.integral_Iic_add_Ioi hLi hRi,
    setIntegral_congr_fun measurableSet_Ioi (fun v hv => exp_abs_Ioi a w v hv),
    setIntegral_congr_fun measurableSet_Iic (fun v hv => exp_abs_Iic a w v hv),
    integral_exp_mul_complex_Ioi hR0, integral_exp_mul_complex_Iic hL0]
  have h1 : ((a : ℂ) - 2 * Real.pi * w * I) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h2 : (-(a : ℂ) - 2 * Real.pi * w * I) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h3 : ((a ^ 2 + 4 * Real.pi ^ 2 * w ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  push_cast at h3 ⊢
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have key : (1 : ℂ) / ((a : ℂ) - 2 * Real.pi * w * I) - 1 / (-(a : ℂ) - 2 * Real.pi * w * I) =
      2 * a / ((a : ℂ) ^ 2 + 4 * (Real.pi : ℂ) ^ 2 * (w : ℂ) ^ 2) := by
    rw [div_sub_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h3]
    linear_combination (-8 * (a : ℂ) * (Real.pi : ℂ) ^ 2 * (w : ℂ) ^ 2) * Complex.I_sq
  rw [← key]
  ring

lemma int_exp_Ioi (c : ℝ) (hc : 0 < c) : ∫ s in Ioi (0:ℝ), Real.exp (-c * s) = 1 / c := by
  rw [integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

lemma integrable_exp_neg_abs (a : ℝ) (ha : 0 < a) :
    Integrable (fun t : ℝ => ((Real.exp (-(a * |t|)) : ℝ) : ℂ)) := by
  have hR : IntegrableOn (fun t : ℝ => ((Real.exp (-(a * |t|)) : ℝ) : ℂ)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (a := -(a:ℂ)) (by simp [ha]) 0).congr_fun
      (fun v hv => by
        simp only
        rw [abs_of_pos (show (0:ℝ) < v from hv)]
        push_cast; ring_nf) measurableSet_Ioi
  have hL : IntegrableOn (fun t : ℝ => ((Real.exp (-(a * |t|)) : ℝ) : ℂ)) (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic (a := (a:ℂ)) (by simp [ha]) 0).congr_fun
      (fun v hv => by
        simp only
        rw [abs_of_nonpos (show v ≤ (0:ℝ) from hv)]
        push_cast; ring_nf) measurableSet_Iic
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0:ℝ))]
  exact hL.union hR

lemma integrable_lorentz (a : ℝ) (ha : 0 < a) :
    Integrable (fun w : ℝ => 2 * a / (a ^ 2 + 4 * Real.pi ^ 2 * w ^ 2)) := by
  have hc : (2 * Real.pi / a) ≠ 0 := by positivity
  have h := (integrable_inv_one_add_sq.comp_mul_left' hc).const_mul (2 / a)
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  have h1 : (1 + (2 * Real.pi / a * w) ^ 2) ≠ 0 := by positivity
  have h2 : a ^ 2 + 4 * Real.pi ^ 2 * w ^ 2 ≠ 0 := by positivity
  simp only
  field_simp
  ring

/-- Subordination: `e^{-a|t|} = ∫₀^∞ 2a e^{-a²s} (π/(4π²s))^{1/2} e^{-(2πt)²/(4·4π²s)} ds`. -/
theorem subord (a : ℝ) (ha : 0 < a) (t : ℝ) :
    ((Real.exp (-(a * |t|)) : ℝ) : ℂ) = ∫ s in Ioi (0:ℝ),
      ((2 * a * Real.exp (-(a ^ 2) * s) : ℝ) : ℂ) *
        (((Real.pi : ℂ) / (4 * (Real.pi : ℂ) ^ 2 * (s : ℂ))) ^ (1 / 2 : ℂ) *
          cexp (-(2 * (Real.pi : ℂ) * (t : ℂ)) ^ 2 / (4 * (4 * (Real.pi : ℂ) ^ 2 * (s : ℂ))))) := by
  set f : ℝ → ℂ := fun t => ((Real.exp (-(a * |t|)) : ℝ) : ℂ) with hf
  have hcont : Continuous f := by fun_prop
  have hint : Integrable f := integrable_exp_neg_abs a ha
  have hF : 𝓕 f = fun w => ((2 * a / (a ^ 2 + 4 * Real.pi ^ 2 * w ^ 2) : ℝ) : ℂ) :=
    funext (fourier_exp_neg_abs a ha)
  have hFint : Integrable (𝓕 f) := by rw [hF]; exact (integrable_lorentz a ha).ofReal
  have hinv := congrFun (hcont.fourierInv_fourier_eq hint hFint) t
  set G : ℝ → ℝ → ℂ := fun w s => cexp (↑(-2 * Real.pi * w * (-t)) * I) •
    ((2 * a * Real.exp (-(a ^ 2 + 4 * Real.pi ^ 2 * w ^ 2) * s) : ℝ) : ℂ) with hG
  have hB : ∀ w : ℝ, 0 < a ^ 2 + 4 * Real.pi ^ 2 * w ^ 2 := fun w => by positivity
  have hinner : ∀ w : ℝ, ((2 * a / (a ^ 2 + 4 * Real.pi ^ 2 * w ^ 2) : ℝ) : ℂ) =
      ∫ s in Ioi (0:ℝ), ((2 * a * Real.exp (-(a ^ 2 + 4 * Real.pi ^ 2 * w ^ 2) * s) : ℝ) : ℂ) := by
    intro w
    rw [integral_complex_ofReal, integral_const_mul, int_exp_Ioi _ (hB w)]
    congr 1; ring
  have hGint : Integrable (Function.uncurry G) (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry G)
        (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
      apply Continuous.aestronglyMeasurable
      simp only [hG, Function.uncurry_def]
      fun_prop
    refine (integrable_prod_iff hmeas).2 ⟨Filter.Eventually.of_forall fun w => ?_, ?_⟩
    · simp only [Function.uncurry_apply_pair, hG, smul_eq_mul]
      exact (((exp_neg_integrableOn_Ioi 0 (hB w)).const_mul (2 * a)).ofReal).const_mul _
    · refine (integrable_lorentz a ha).congr (Filter.Eventually.of_forall fun w => ?_)
      simp only [Function.uncurry_apply_pair, hG, smul_eq_mul, norm_mul,
        Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_two, abs_of_pos ha, Real.abs_exp]
      rw [integral_const_mul, int_exp_Ioi _ (hB w)]
      ring
  show f t = _
  rw [← hinv, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul, hF]
  simp_rw [hinner, ← integral_smul]
  rw [integral_integral_swap hGint]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hs' : (0:ℝ) < s := hs
  have hpt : ∀ w : ℝ, G w s = ((2 * a * Real.exp (-(a ^ 2) * s) : ℝ) : ℂ) *
      (cexp (I * (2 * (Real.pi : ℂ) * (t : ℂ)) * (w : ℂ)) *
        cexp (-(4 * (Real.pi : ℂ) ^ 2 * (s : ℂ)) * (w : ℂ) ^ 2)) := by
    intro w
    simp only [hG, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_exp]
    rw [← Complex.exp_add, mul_comm (cexp _), mul_assoc, ← Complex.exp_add,
      mul_assoc _ (cexp _) (cexp _), ← Complex.exp_add]
    congr 2
    push_cast; ring
  simp only [hpt]
  have hb : 0 < (4 * (Real.pi : ℂ) ^ 2 * (s : ℂ)).re := by
    rw [show (4 * (Real.pi : ℂ) ^ 2 * (s : ℂ)) = ((4 * Real.pi ^ 2 * s : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
    exact mul_pos (by positivity) hs'
  rw [integral_const_mul, fourierIntegral_gaussian hb]

/-- `∫₀^∞ s e^{-Bs} ds = 1/B²`. -/
lemma int_s_exp_Ioi (B : ℝ) (hB : 0 < B) :
    ∫ s in Ioi (0:ℝ), s * Real.exp (-B * s) = 1 / B ^ 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 1) (b := B) one_pos
    (by norm_num) hB
  simp only [Real.rpow_one] at h
  rw [h, show (-(1 + 1) / 1 : ℝ) = -2 by norm_num, show ((1 + 1) / 1 : ℝ) = 2 by norm_num,
    Real.Gamma_two, Real.rpow_neg hB.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  field_simp

lemma integrableOn_s_exp (B : ℝ) (hB : 0 < B) :
    IntegrableOn (fun s : ℝ => s * Real.exp (-B * s)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := B) (by norm_num)
    one_pos hB
  simpa only [Real.rpow_one] using h

/-- Real weight `2u e^{-u²s} (4πs)^{-1/2}`. -/
noncomputable def Kw (u s : ℝ) : ℝ := 2 * u * Real.exp (-(u ^ 2) * s) * ((4 * Real.pi * s)⁻¹) ^ (1 / 2 : ℝ)

lemma rcombine (s : ℝ) (hs : 0 < s) :
    ((4 * Real.pi * s)⁻¹) ^ (1 / 2 : ℝ) * (Real.pi / (1 / (4 * s))) ^ (3 / 2 : ℝ) = 4 * Real.pi * s := by
  have hX : 0 < 4 * Real.pi * s := mul_pos (by positivity) hs
  rw [show Real.pi / (1 / (4 * s)) = 4 * Real.pi * s by field_simp, Real.inv_rpow hX.le,
    show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hX, Real.rpow_one]
  have : (0:ℝ) < (4 * Real.pi * s) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hX _
  field_simp

lemma subord3 {V : Type*} [NormedAddCommGroup V] (u : ℝ) (hu : 0 < u) (x : V) :
    ((Real.exp (-(u * ‖x‖)) : ℝ) : ℂ) = ∫ s in Ioi (0:ℝ),
      ((Kw u s : ℝ) : ℂ) * cexp (-(1 / (4 * (s:ℂ))) * ((‖x‖ : ℝ) : ℂ) ^ 2) := by
  have h := subord u hu ‖x‖
  rw [abs_of_nonneg (norm_nonneg x)] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hs' : (0:ℝ) < s := hs
  have hX : 0 < 4 * Real.pi * s := mul_pos (by positivity) hs'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs'.ne'
  have e1 : ((Real.pi : ℂ) / (4 * (Real.pi : ℂ) ^ 2 * (s : ℂ))) ^ (1 / 2 : ℂ) =
      ((((4 * Real.pi * s)⁻¹) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (inv_nonneg.2 hX.le)]
    congr 1
    · push_cast; field_simp
    · push_cast; ring
  have e2 : -(2 * (Real.pi:ℂ) * ((‖x‖:ℝ):ℂ)) ^ 2 / (4 * (4 * (Real.pi:ℂ) ^ 2 * (s:ℂ))) =
      -(1 / (4 * (s:ℂ))) * ((‖x‖:ℝ):ℂ) ^ 2 := by
    field_simp; ring
  rw [e2, Kw, Complex.ofReal_mul ((2 * u * Real.exp (-(u ^ 2) * s))), ← e1]
  ring

lemma norm_F {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u s : ℝ) (hu : 0 < u) (hs : 0 < s) (x ξ : V) :
    ‖cexp (↑(-2 * Real.pi * inner ℝ x ξ) * I) •
      (((Kw u s : ℝ) : ℂ) * cexp (-(1 / (4 * (s:ℂ))) * ((‖x‖ : ℝ) : ℂ) ^ 2))‖ =
      Kw u s * Real.exp (-(1 / (4 * s)) * ‖x‖ ^ 2) := by
  have hK : 0 ≤ Kw u s := by unfold Kw; positivity
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hK,
    show (-(1 / (4 * (s:ℂ))) * ((‖x‖ : ℝ) : ℂ) ^ 2) = ((-(1 / (4 * s)) * ‖x‖ ^ 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_exp_ofReal]

/-- 3D Fourier transform of `e^{-u|x|}`: `8πu/(u²+4π²|ξ|²)²`. -/
theorem fourier_exp_neg_norm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (hV : Module.finrank ℝ V = 3) (u : ℝ) (hu : 0 < u) (ξ : V) :
    𝓕 (fun x : V => ((Real.exp (-(u * ‖x‖)) : ℝ) : ℂ)) ξ =
      ((8 * Real.pi * u / (u ^ 2 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
  set F : V → ℝ → ℂ := fun x s => cexp (↑(-2 * Real.pi * inner ℝ x ξ) * I) •
    (((Kw u s : ℝ) : ℂ) * cexp (-(1 / (4 * (s:ℂ))) * ((‖x‖ : ℝ) : ℂ) ^ 2)) with hFdef
  have hB : 0 < u ^ 2 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have hbre : ∀ s : ℝ, 0 < s → 0 < (1 / (4 * (s:ℂ))).re := fun s hs => by
    rw [show (1 / (4 * (s:ℂ))) = ((1 / (4 * s) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    exact div_pos one_pos (mul_pos four_pos hs)
  have hgint : ∀ s : ℝ, 0 < s → Integrable (fun x => F x s) := fun s hs => by
    have h := ((GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (hbre s hs)
      (-(2 * (Real.pi : ℂ) * I)) ξ).const_mul ((Kw u s : ℝ) : ℂ))
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hFdef, smul_eq_mul]
    rw [Complex.exp_add, real_inner_comm]
    push_cast; ring_nf
  have hnormint : ∀ s : ℝ, 0 < s → ∫ x, ‖F x s‖ = 8 * Real.pi * u * (s * Real.exp (-(u ^ 2) * s)) := by
    intro s hs
    simp only [hFdef, norm_F u s hu hs]
    rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (div_pos one_pos (mul_pos four_pos hs)), hV]
    rw [show ((3:ℕ):ℝ) / 2 = 3 / 2 by norm_num, Kw, mul_assoc, rcombine s hs]
    ring
  have hFint : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry F)
        (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
      apply Measurable.aestronglyMeasurable
      simp only [hFdef, Function.uncurry_def, Kw]
      fun_prop
    refine (integrable_prod_iff' hmeas).2 ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hgint s hs
    · refine IntegrableOn.congr_fun (f := fun s => 8 * Real.pi * u * (s * Real.exp (-(u ^ 2) * s)))
        ((integrableOn_s_exp (u ^ 2) (by positivity)).const_mul (8 * Real.pi * u))
        (fun s hs => ?_) measurableSet_Ioi
      simp only [Function.uncurry_apply_pair]
      rw [hnormint s hs]
  have hgauss : ∀ s : ℝ, 0 < s → ∫ x : V, F x s =
      ((8 * Real.pi * u * (s * Real.exp (-(u ^ 2 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * s)) : ℝ) : ℂ) := by
    intro s hs
    have hG := fourier_gaussian_innerProductSpace (hbre s hs) ξ (V := V)
    rw [Real.fourier_eq', hV] at hG
    calc
      ∫ x : V, F x s = ((Kw u s : ℝ) : ℂ) * ∫ v : V, cexp (↑(-2 * Real.pi * inner ℝ v ξ) * I) •
          cexp (-(1 / (4 * (s:ℂ))) * ((‖v‖ : ℝ) : ℂ) ^ 2) := by
        rw [← integral_const_mul]
        congr 1; funext x
        simp only [hFdef, smul_eq_mul]; ring
      _ = _ := by
        rw [hG]
        have hX : 0 ≤ Real.pi / (1 / (4 * s)) := by positivity
        rw [show ((Real.pi:ℂ) / (1 / (4 * (s:ℂ)))) = ((Real.pi / (1 / (4 * s)) : ℝ) : ℂ) by
            push_cast; ring,
          show (((3:ℕ):ℂ) / 2) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hX,
          show (-(Real.pi:ℂ) ^ 2 * ((‖ξ‖:ℝ):ℂ) ^ 2 / (1 / (4 * (s:ℂ)))) =
            ((-(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * s : ℝ) : ℂ) by
            have hs0 : (s:ℂ) ≠ 0 := by exact_mod_cast hs.ne'
            push_cast; field_simp,
          ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
        congr 1
        have hr := rcombine s hs
        have hq : Real.exp (-(u ^ 2 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * s) =
            Real.exp (-(u ^ 2) * s) * Real.exp (-(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * s) := by
          rw [← Real.exp_add]; ring_nf
        unfold Kw
        linear_combination (2 * u * Real.exp (-(u ^ 2) * s) *
          Real.exp (-(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * s)) * hr - (8 * Real.pi * u * s) * hq
  calc 𝓕 (fun x : V => ((Real.exp (-(u * ‖x‖)) : ℝ) : ℂ)) ξ
      = ∫ x : V, ∫ s in Ioi (0:ℝ), F x s := by
        rw [Real.fourier_eq']
        congr 1; funext x
        rw [subord3 u hu x, ← integral_smul]
    _ = ∫ s in Ioi (0:ℝ), ∫ x : V, F x s := integral_integral_swap hFint
    _ = ∫ s in Ioi (0:ℝ), ((8 * Real.pi * u * (s * Real.exp (-(u ^ 2 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * s)) : ℝ) : ℂ) :=
        setIntegral_congr_fun measurableSet_Ioi (fun s hs => hgauss s hs)
    _ = _ := by
        rw [integral_complex_ofReal, integral_const_mul, int_s_exp_Ioi _ hB]
        congr 1; ring

end HVZHyd


/-! L¹ ∩ L² agreement of the `L²` Fourier transform with the integral Fourier transform. -/

set_option autoImplicit false

open MeasureTheory FourierTransform SchwartzMap
open scoped ContDiff

namespace HVZHyd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem continuous_fourier_of_integrable (f : E → ℂ) (hf1 : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous (L := innerₗ E) Real.continuous_fourierChar
    continuous_inner hf1

theorem pairing_fourier (f : E → ℂ) (hf1 : Integrable f) (u : 𝓢(E, ℂ)) :
    ∫ x, (𝓕 u) x • f x = ∫ x, u x • 𝓕 f x := by
  simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ E)
      Real.continuous_fourierChar continuous_inner u.integrable hf1)

theorem Lp_fourier_eq_integral (f : E → ℂ) (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (((Lp.fourierTransformₗᵢ E ℂ) (hf2.toLp f) : Lp ℂ 2 (volume : Measure E)) : E → ℂ)
      =ᵐ[volume] 𝓕 f := by
  have key : ∀ u : 𝓢(E, ℂ),
      ∫ x, u x • ((Lp.fourierTransformₗᵢ E ℂ) (hf2.toLp f) : E → ℂ) x = ∫ x, u x • 𝓕 f x := by
    intro u
    have h1 := congrArg (fun T : 𝓢'(E, ℂ) => T u)
      (Lp.fourier_toTemperedDistribution_eq (hf2.toLp f))
    simp only [Lp.toTemperedDistribution_apply, TemperedDistribution.fourier_apply] at h1
    have h2 : ∫ x, (𝓕 u) x • (hf2.toLp f : E → ℂ) x = ∫ x, (𝓕 u) x • f x :=
      integral_congr_ae (by filter_upwards [hf2.coeFn_toLp] with x hx; rw [hx])
    rw [← pairing_fourier f hf1 u, ← h2]
    exact h1.symm
  have hL : LocallyIntegrable
      (((Lp.fourierTransformₗᵢ E ℂ) (hf2.toLp f) : Lp ℂ 2 (volume : Measure E)) : E → ℂ)
      volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hR : LocallyIntegrable (𝓕 f) volume :=
    (continuous_fourier_of_integrable f hf1).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hL hR (fun g hg hgs => ?_)
  have hgc : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hgcs : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) := hgs.comp_left Complex.ofReal_zero
  have := key (hgcs.toSchwartzMap hgc)
  simp only [Complex.real_smul, smul_eq_mul]
  exact this

end HVZHyd


set_option autoImplicit false

open MeasureTheory FourierTransform Complex Set Filter Topology

namespace HVZHyd

lemma int_lorentz2 (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c) :
    ∫ u in Ioi a, 8 * Real.pi * u / (u ^ 2 + c) ^ 2 = 4 * Real.pi / (a ^ 2 + c) := by
  have hd : ∀ u ∈ Ici a, HasDerivAt (fun u : ℝ => -(4 * Real.pi / (u ^ 2 + c)))
      (8 * Real.pi * u / (u ^ 2 + c) ^ 2) u := by
    intro u hu
    have hu' : 0 < u := lt_of_lt_of_le ha hu
    have hu0 : 0 < u ^ 2 + c := by positivity
    have h1 := (((hasDerivAt_pow 2 u).add_const c).inv hu0.ne').const_mul (-(4 * Real.pi))
    have e2 : -(4 * Real.pi) * (-(((2 : ℕ) : ℝ) * u ^ (2 - 1)) / (u ^ 2 + c) ^ 2) =
        8 * Real.pi * u / (u ^ 2 + c) ^ 2 := by norm_num; ring
    refine (h1.congr_deriv e2).congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
    simp only [Pi.inv_apply]
    ring
  have ht : Tendsto (fun u : ℝ => -(4 * Real.pi / (u ^ 2 + c))) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := 4 * Real.pi)).div_atTop
      (tendsto_atTop_add_const_right _ c (tendsto_pow_atTop (two_ne_zero)))
    simpa using this.neg
  have hpos : ∀ u ∈ Ioi a, 0 ≤ 8 * Real.pi * u / (u ^ 2 + c) ^ 2 := by
    intro u hu
    have hu' : 0 < u := ha.trans hu
    positivity
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_Ioi_deriv_of_nonneg' hd hpos ht) ht]
  ring

lemma exp_div_int (a r : ℝ) (hr : 0 < r) :
    ∫ u in Ioi a, Real.exp (-(u * r)) = Real.exp (-(a * r)) / r := by
  have h := integral_exp_mul_Ioi (neg_neg_of_pos hr) a
  have e : ∀ u : ℝ, -(u * r) = -r * u := fun u => by ring
  simp_rw [e]
  rw [h]
  field_simp

lemma cexp_div_int (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 0 ≤ r) :
    ((Real.exp (-(a * r)) / r : ℝ) : ℂ) = ∫ u in Ioi a, ((Real.exp (-(u * r)) : ℝ) : ℂ) := by
  rw [integral_complex_ofReal]
  rcases hr.lt_or_eq with hr | hr
  · rw [exp_div_int a r hr]
  · subst hr
    simp [Measure.real]

/-- Radial integrability in a 3-dimensional space: `‖x‖^s e^{-b‖x‖}` for `s > -3`. -/
lemma integrable_radial {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (hV : Module.finrank ℝ V = 3) (s : ℝ) (hs : -3 < s) (b : ℝ) (hb : 0 < b) :
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

lemma integrable_exp_norm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (hV : Module.finrank ℝ V = 3) (u : ℝ) (hu : 0 < u) :
    Integrable (fun x : V => Real.exp (-(u * ‖x‖))) := by
  refine (integrable_radial hV 0 (by norm_num) u hu).congr (Eventually.of_forall fun x => ?_)
  simp

/-- 3D Fourier transform of the Yukawa potential `e^{-a|x|}/|x|`: `4π/(a²+4π²|ξ|²)`. -/
theorem fourier_yukawa {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (hI : ∀ u : ℝ, 0 < u → Integrable (fun x : V => Real.exp (-(u * ‖x‖))))
    (hF : ∀ u : ℝ, 0 < u → ∀ ξ : V, 𝓕 (fun x : V => ((Real.exp (-(u * ‖x‖)) : ℝ) : ℂ)) ξ =
      ((8 * Real.pi * u / (u ^ 2 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ))
    (a : ℝ) (ha : 0 < a) (ξ : V) :
    𝓕 (fun x : V => ((Real.exp (-(a * ‖x‖)) / ‖x‖ : ℝ) : ℂ)) ξ =
      ((4 * Real.pi / (a ^ 2 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
  set G : V → ℝ → ℂ := fun x u => cexp (↑(-2 * Real.pi * inner ℝ x ξ) * I) •
    ((Real.exp (-(u * ‖x‖)) : ℝ) : ℂ) with hG
  have hnorm : ∀ x u, ‖G x u‖ = Real.exp (-(u * ‖x‖)) := by
    intro x u
    simp only [hG]
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hint0 : ∀ u : ℝ, 0 < u → ∫ x : V, Real.exp (-(u * ‖x‖)) = 8 * Real.pi * u ^ (-3 : ℝ) := by
    intro u hu
    have h := hF u hu 0
    rw [Real.fourier_eq'] at h
    simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      one_smul, norm_zero] at h
    rw [integral_complex_ofReal] at h
    rw [Complex.ofReal_injective h, Real.rpow_neg hu.le,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hu0 : u ≠ 0 := hu.ne'
    field_simp
    ring
  have hGint : Integrable (Function.uncurry G) (volume.prod (volume.restrict (Ioi a))) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry G)
        (volume.prod (volume.restrict (Ioi a))) := by
      apply Measurable.aestronglyMeasurable
      simp only [hG, Function.uncurry_def]
      fun_prop
    refine (integrable_prod_iff' hmeas).2 ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      refine Integrable.mono' (hI u (ha.trans hu)) ?_ (Eventually.of_forall fun x => (hnorm x u).le)
      apply Measurable.aestronglyMeasurable
      simp only [hG]
      fun_prop
    · refine IntegrableOn.congr_fun ((integrableOn_Ioi_rpow_of_lt (a := -3) (by norm_num) ha).const_mul
        (8 * Real.pi)) (fun u hu => ?_) measurableSet_Ioi
      simp only [Function.uncurry_apply_pair, hnorm]
      rw [hint0 u (ha.trans hu)]
  calc 𝓕 (fun x : V => ((Real.exp (-(a * ‖x‖)) / ‖x‖ : ℝ) : ℂ)) ξ
      = ∫ x : V, ∫ u in Ioi a, G x u := by
        rw [Real.fourier_eq']
        congr 1; funext x
        simp only [hG]
        rw [integral_smul, cexp_div_int a ha ‖x‖ (norm_nonneg x)]
    _ = ∫ u in Ioi a, ∫ x : V, G x u := integral_integral_swap hGint
    _ = ∫ u in Ioi a, ((8 * Real.pi * u / (u ^ 2 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
        rw [← hF u (ha.trans hu) ξ, Real.fourier_eq']
    _ = _ := by
        rw [integral_complex_ofReal, int_lorentz2 a _ ha (by positivity)]

end HVZHyd


/-! C4 (hydrogen) building blocks for 7ab9d8bf. -/

namespace HVZHyd
open TeschlQM.Shared TeschlQM.Atomic MeasureTheory

/-- An eigenvalue lies in the spectrum: `ψ = R (A - z) ψ = R 0 = 0`. -/
theorem mem_spectrum_of_eigen {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) (ψ : A.domain) (hψ : (ψ : H) ≠ 0) (h : A ψ = z • (ψ : H)) :
    z ∈ TeschlQM.Shared.spectrum A := by
  rintro ⟨R, -, h2⟩
  have := h2 ψ
  rw [h, sub_self, map_zero] at this
  exact hψ this.symm

/-- Eigenvector of the operator sum `H₀ + V` from eigen-data on the two summands. -/
theorem mem_spectrum_add_of_eigen {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ.[ℂ] H) (z : ℂ) (ψ : H) (hA : ψ ∈ A.domain) (hB : ψ ∈ B.domain) (hψ : ψ ≠ 0)
    (h : A ⟨ψ, hA⟩ + B ⟨ψ, hB⟩ = z • ψ) : z ∈ TeschlQM.Shared.spectrum (A + B) := by
  refine mem_spectrum_of_eigen (A + B) z ⟨ψ, ⟨hA, hB⟩⟩ hψ ?_
  rw [LinearPMap.add_apply]
  exact h

end HVZHyd

namespace HVZHyd

open TeschlQM.Shared TeschlQM.Atomic MeasureTheory FourierTransform Complex Set Filter

lemma norm_electron_one (x : EuclideanSpace ℝ (Fin 1 × Fin 3)) : ‖electron x 0‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1

lemma atomicPotential_one (γne γee : ℝ) (x : EuclideanSpace ℝ (Fin 1 × Fin 3)) :
    atomicPotential γne γee 1 x = -(γne / ‖x‖) := by
  have h2 : ∑ j : Fin 1, ∑ k ∈ Finset.univ.filter (fun k : Fin 1 => j < k),
      γee / ‖electron x j - electron x k‖ = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_filter] at hk
    exact absurd hk.2 (by rw [Subsingleton.elim j k]; exact lt_irrefl k)
  unfold atomicPotential
  rw [h2, Fin.sum_univ_one, norm_electron_one]
  ring

theorem hyd_core (γne γee : ℝ) (hne : 0 < γne)
    (hFψ : ∀ ξ : EuclideanSpace ℝ (Fin 1 × Fin 3),
      𝓕 (fun x : EuclideanSpace ℝ (Fin 1 × Fin 3) => ((Real.exp (-(γne / 2 * ‖x‖)) : ℝ) : ℂ)) ξ =
        ((8 * Real.pi * (γne / 2) / ((γne / 2) ^ 2 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ))
    (hFy : ∀ ξ : EuclideanSpace ℝ (Fin 1 × Fin 3),
      𝓕 (fun x : EuclideanSpace ℝ (Fin 1 × Fin 3) =>
        ((Real.exp (-(γne / 2 * ‖x‖)) / ‖x‖ : ℝ) : ℂ)) ξ =
        ((4 * Real.pi / ((γne / 2) ^ 2 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) : ℝ) : ℂ)) :
    (((-(γne ^ 2 / 4) : ℝ)) : ℂ) ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee 1) := by
  have hV : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1 × Fin 3)) = 3 := by simp
  have hz : (((-(γne ^ 2 / 4) : ℝ)) : ℂ) = -(((γne / 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hz]
  set a : ℝ := γne / 2 with ha_def
  have ha : 0 < a := by positivity
  have hγ : (γne : ℂ) = 2 * (a : ℂ) := by rw [ha_def]; push_cast; ring
  set ψf : EuclideanSpace ℝ (Fin 1 × Fin 3) → ℂ :=
    fun x => ((Real.exp (-(a * ‖x‖)) : ℝ) : ℂ) with hψf
  set yf : EuclideanSpace ℝ (Fin 1 × Fin 3) → ℂ :=
    fun x => ((Real.exp (-(a * ‖x‖)) / ‖x‖ : ℝ) : ℂ) with hyf
  have hψm : AEStronglyMeasurable ψf := by
    apply Measurable.aestronglyMeasurable; simp only [hψf]; fun_prop
  have hym : AEStronglyMeasurable yf := by
    apply Measurable.aestronglyMeasurable; simp only [hyf]; fun_prop
  have hψ1 : Integrable ψf := (integrable_exp_norm hV a ha).ofReal
  have hψ2 : MemLp ψf 2 := by
    rw [memLp_two_iff_integrable_sq_norm hψm]
    refine (integrable_exp_norm hV (2 * a) (by positivity)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [hψf]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), sq, ← Real.exp_add]
    ring_nf
  have hy1 : Integrable yf := by
    refine ((integrable_radial hV (-1) (by norm_num) a ha).ofReal).congr
      (Eventually.of_forall fun x => ?_)
    simp only [hyf]
    rw [Real.rpow_neg_one, div_eq_mul_inv, mul_comm]
    rfl
  have hy2 : MemLp yf 2 := by
    rw [memLp_two_iff_integrable_sq_norm hym]
    refine (integrable_radial hV (-2) (by norm_num) (2 * a) (by positivity)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [hyf]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.rpow_neg (norm_nonneg _), Real.rpow_two,
      div_pow, sq (Real.exp _), ← Real.exp_add]
    ring_nf
  set FL := Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin 1 × Fin 3)) ℂ with hFL
  set Ψ := hψ2.toLp ψf with hΨ
  set Y := hy2.toLp yf with hY
  have hΨF := Lp_fourier_eq_integral ψf hψ1 hψ2
  have hYF := Lp_fourier_eq_integral yf hy1 hy2
  set m : EuclideanSpace ℝ (Fin 1 × Fin 3) → ℂ :=
    fun ξ => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) with hm
  have hkey : ∀ ξ, m ξ * 𝓕 ψf ξ = (γne : ℂ) * 𝓕 yf ξ - ((a ^ 2 : ℝ) : ℂ) * 𝓕 ψf ξ := by
    intro ξ
    have hD : 0 < a ^ 2 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
    have hD' : ((a : ℂ) ^ 2 + 4 * (Real.pi : ℂ) ^ 2 * ((‖ξ‖ : ℝ) : ℂ) ^ 2) ≠ 0 := by
      exact_mod_cast hD.ne'
    rw [hFψ ξ, hFy ξ, hγ]
    simp only [hm]
    push_cast
    field_simp
    ring
  have hdomA : MemLp (fun ξ => m ξ * (FL Ψ : EuclideanSpace ℝ (Fin 1 × Fin 3) → ℂ) ξ) 2 := by
    refine (((Lp.memLp (FL Y)).const_smul (γne : ℂ)).sub
      ((Lp.memLp (FL Ψ)).const_smul ((a ^ 2 : ℝ) : ℂ))).ae_eq ?_
    filter_upwards [hΨF, hYF] with ξ h1 h2
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1, h2, hkey ξ]
  have hA : Ψ ∈ (freeHamiltonian (Fin 1 × Fin 3)).domain := Submodule.mem_comap.2 hdomA
  have hVfun : ∀ x : EuclideanSpace ℝ (Fin 1 × Fin 3),
      ((atomicPotential γne γee 1 x : ℝ) : ℂ) * ψf x = -(γne : ℂ) * yf x := by
    intro x
    rw [atomicPotential_one]
    simp only [hψf, hyf]
    push_cast
    ring
  have hdomB : MemLp (fun x => ((atomicPotential γne γee 1 x : ℝ) : ℂ) *
      (Ψ : EuclideanSpace ℝ (Fin 1 × Fin 3) → ℂ) x) 2 := by
    refine (hy2.const_mul (-(γne : ℂ))).ae_eq ?_
    filter_upwards [hψ2.coeFn_toLp] with x hx
    rw [hx, hVfun]
  have hB : Ψ ∈ (mulOp volume (fun x => ((atomicPotential γne γee 1 x : ℝ) : ℂ))).domain := hdomB
  have hΨne : Ψ ≠ 0 := by
    intro h0
    have h1 : ψf =ᵐ[volume] 0 :=
      hψ2.coeFn_toLp.symm.trans (by rw [← hΨ, h0]; exact Lp.coeFn_zero _ _ _)
    obtain ⟨x, hx⟩ := h1.exists
    exact (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne') hx
  have hAval : freeHamiltonian (Fin 1 × Fin 3) ⟨Ψ, hA⟩ = FL.symm (hdomA.toLp _) := rfl
  have hBval : mulOp volume (fun x => ((atomicPotential γne γee 1 x : ℝ) : ℂ)) ⟨Ψ, hB⟩ =
      hdomB.toLp _ := rfl
  have hT1 : hdomA.toLp _ = (γne : ℂ) • FL Y - ((a ^ 2 : ℝ) : ℂ) • FL Ψ := by
    refine Lp.ext ?_
    filter_upwards [hdomA.coeFn_toLp, Lp.coeFn_sub ((γne : ℂ) • FL Y) (((a ^ 2 : ℝ) : ℂ) • FL Ψ),
      Lp.coeFn_smul (γne : ℂ) (FL Y), Lp.coeFn_smul ((a ^ 2 : ℝ) : ℂ) (FL Ψ), hΨF, hYF]
      with ξ h1 h2 h3 h4 h5 h6
    rw [h1, h2, Pi.sub_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      h5, h6, hkey ξ]
  have hT2 : hdomB.toLp _ = (-(γne : ℂ)) • Y := by
    refine Lp.ext ?_
    filter_upwards [hdomB.coeFn_toLp, Lp.coeFn_smul (-(γne : ℂ)) Y, hψ2.coeFn_toLp,
      hy2.coeFn_toLp] with x h1 h2 h3 h4
    rw [h1, h2, Pi.smul_apply, smul_eq_mul, h3, h4, hVfun]
  refine mem_spectrum_add_of_eigen (freeHamiltonian (Fin 1 × Fin 3))
    (mulOp volume (fun x => ((atomicPotential γne γee 1 x : ℝ) : ℂ))) _ Ψ hA hB hΨne ?_
  rw [hAval, hBval, hT1, hT2]
  simp only [map_sub, map_smul, LinearIsometryEquiv.symm_apply_apply]
  rw [neg_smul, neg_smul]
  abel

end HVZHyd


open TeschlQM.Atomic in
theorem solution (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) :
    (((-(γne ^ 2 / 4) : ℝ)) : ℂ) ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee 1) := by
  have hV : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1 × Fin 3)) = 3 := by simp
  have ha : 0 < γne / 2 := by positivity
  exact HVZHyd.hyd_core γne γee hne (fun ξ => HVZHyd.fourier_exp_neg_norm hV (γne / 2) ha ξ)
    (fun ξ => HVZHyd.fourier_yukawa (fun u hu => HVZHyd.integrable_exp_norm hV u hu)
      (fun u hu ξ => HVZHyd.fourier_exp_neg_norm hV u hu ξ) (γne / 2) ha ξ)

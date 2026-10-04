-- Prove2me | solution 1 for ReflectionlessPotential.completeness_relation
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T11:26:17.738168+00:00
-- url     : https://prove2.me/submissions/a41ce534-5ea8-488a-83e7-7c0e5246d2d3

import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Probability.Distributions.Cauchy
import Definitions.Def_ReflectionlessPotentialDefs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity

open MeasureTheory FourierTransform SchwartzMap
open scoped Real ContDiff

set_option backward.isDefEq.respectTransparency false

/-- On L¹ ∩ L² the ordinary Fourier integral agrees almost everywhere with
the L² Fourier isometry. -/
theorem fourier_integral_agrees_L2 (f : ℝ → ℂ) (hf : Integrable f)
    (hf2 : MemLp f 2 volume) :
    (fun x => (𝓕 (hf2.toLp f) : Lp (α := ℝ) ℂ 2 volume) x) =ᵐ[volume] 𝓕 f := by
  let p : Lp (α := ℝ) ℂ 2 volume := hf2.toLp f
  let F : Lp (α := ℝ) ℂ 2 volume := 𝓕 p
  have hc : Continuous (𝓕 f) := by
    have hf1 : MemLp f 1 volume := memLp_one_iff_integrable.mpr hf
    rw [← Real.fourierTransform_toLp hf1]
    exact (Real.Lp.fourierTransform (hf1.toLp f)).continuous
  apply ae_eq_of_integral_contDiff_smul_eq (Lp.memLp F |>.locallyIntegrable (by norm_num))
    hc.locallyIntegrable
  intro g hg hgs
  have hgcpt : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgs.comp_left rfl
  have hgdiff : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let φ : 𝓢(ℝ, ℂ) := hgcpt.toSchwartzMap hgdiff
  have hd := congrArg (fun D : 𝓢'(ℝ, ℂ) => D φ) (Lp.fourier_toTemperedDistribution_eq p)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] at hd
  have hd' : ∫ x : ℝ, φ x * F x = ∫ x : ℝ, (𝓕 φ) x * f x := by
    rw [← hd]
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  have hswap : ∫ x : ℝ, (𝓕 φ) x * f x = ∫ x : ℝ, φ x * (𝓕 f) x := by
    have hs := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (μ := volume) (ν := volume) (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner φ.integrable hf
    have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
      ext
      rfl
    rw [hflip] at hs
    simpa only [SchwartzMap.fourier_coe, smul_eq_mul] using! hs
  simpa [φ, Complex.real_smul] using hd'.trans hswap

theorem fourier_integral_memLp (f : ℝ → ℂ) (hf : Integrable f)
    (hf2 : MemLp f 2 volume) : MemLp (𝓕 f) 2 volume :=
  MemLp.ae_eq (fourier_integral_agrees_L2 f hf hf2)
    (Lp.memLp (𝓕 (hf2.toLp f) : Lp (α := ℝ) ℂ 2 volume))

theorem fourier_integral_norm_sq (f : ℝ → ℂ) (hf : Integrable f)
    (hf2 : MemLp f 2 volume) :
    ∫ x : ℝ, ‖(𝓕 f) x‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  let p : Lp (α := ℝ) ℂ 2 volume := hf2.toLp f
  let F : Lp (α := ℝ) ℂ 2 volume := 𝓕 p
  have hL2 : ∫ x : ℝ, ‖F x‖ ^ 2 = ∫ x : ℝ, ‖p x‖ ^ 2 := by
    apply Complex.ofRealLI.injective
    have hp := Lp.inner_fourier_eq p p
    rw [L2.inner_def, L2.inner_def] at hp
    simp_rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at hp
    rw [integral_ofReal, integral_ofReal] at hp
    exact hp
  calc
    ∫ x : ℝ, ‖(𝓕 f) x‖ ^ 2 = ∫ x : ℝ, ‖F x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [fourier_integral_agrees_L2 f hf hf2] with x hx
      rw [hx]
    _ = ∫ x : ℝ, ‖p x‖ ^ 2 := hL2
    _ = ∫ x : ℝ, ‖f x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp] with x hx
      rw [hx]

theorem fourier_integral_pairing (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g)
    (hf2 : MemLp f 2 volume) (hg2 : MemLp g 2 volume) :
    ∫ x : ℝ, star ((𝓕 f) x) * (𝓕 g) x = ∫ x : ℝ, star (f x) * g x := by
  let p : Lp (α := ℝ) ℂ 2 volume := hf2.toLp f
  let q : Lp (α := ℝ) ℂ 2 volume := hg2.toLp g
  have hp := Lp.inner_fourier_eq p q
  rw [L2.inner_def, L2.inner_def] at hp
  simp only [RCLike.inner_apply'] at hp
  calc
    ∫ x : ℝ, star ((𝓕 f) x) * (𝓕 g) x =
        ∫ x : ℝ, star ((𝓕 p : Lp (α := ℝ) ℂ 2 volume) x) *
          (𝓕 q : Lp (α := ℝ) ℂ 2 volume) x := by
      apply integral_congr_ae
      filter_upwards [fourier_integral_agrees_L2 f hf hf2,
        fourier_integral_agrees_L2 g hg hg2] with x hx hy
      rw [hx, hy]
    _ = ∫ x : ℝ, star (p x) * q x := hp
    _ = ∫ x : ℝ, star (f x) * g x := by
      apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp, hg2.coeFn_toLp] with x hx hy
      rw [hx, hy]


open MeasureTheory ContinuousLinearMap
open scoped Convolution

set_option backward.isDefEq.respectTransparency false

theorem integrable_bounded_memLp_two (f : ℝ → ℂ) (hf : Integrable f) (C : ℝ)
    (hb : ∀ x, ‖f x‖ ≤ C) : MemLp f 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  have hh : ∀ᵐ x : ℝ, ‖‖f x‖‖ ≤ C := Filter.Eventually.of_forall fun x => by simpa using hb x
  simpa only [pow_two] using hf.norm.mul_bdd hf.aestronglyMeasurable.norm hh

theorem convolution_integrable_bounded_memLp (a f : ℝ → ℂ) (ha : Integrable a)
    (hf : Integrable f) (hc : Continuous f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    MemLp (a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) 2 volume := by
  have hi := ha.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf
  apply integrable_bounded_memLp_two _ hi ((∫ x : ℝ, ‖a x‖) * C)
  intro x
  have hm : AEStronglyMeasurable (fun y : ℝ => f (x - y)) volume :=
    (hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hp : Integrable (fun y : ℝ => a y * f (x - y)) :=
    ha.mul_bdd hm (Filter.Eventually.of_forall fun y => hb (x - y))
  change ‖∫ y : ℝ, a y * f (x - y)‖ ≤ _
  calc
    ‖∫ y : ℝ, a y * f (x - y)‖ ≤ ∫ y : ℝ, ‖a y * f (x - y)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, ‖a y‖ * C := by
      apply integral_mono hp.norm (ha.norm.mul_const C)
      intro y
      change ‖a y * f (x - y)‖ ≤ ‖a y‖ * C
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb (x - y)) (norm_nonneg _)
    _ = (∫ y : ℝ, ‖a y‖) * C := integral_mul_const _ _

theorem multiplier_convolution_pairing (a f g : ℝ → ℂ)
    (ha : Integrable a) (hf : Integrable f) (hg : Integrable g)
    (hc : Continuous f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C)
    (hg2 : MemLp g 2 volume) :
    ∫ x : ℝ, star ((𝓕 g) x) * ((𝓕 a) x * (𝓕 f) x) =
      ∫ x : ℝ, star (g x) * (a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x := by
  have hcv := ha.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf
  have hc2 := convolution_integrable_bounded_memLp a f ha hf hc C hb
  have hd := fourier_integral_pairing g (a ⋆[ContinuousLinearMap.mul ℂ ℂ] f)
    hg hcv hg2 hc2
  simp_rw [Real.fourier_mul_convolution_eq ha hf] at hd
  exact hd


open Complex MeasureTheory Set Real
open scoped FourierTransform RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false

theorem laplace_transform (a w : ℝ) (ha : 0 < a) :
    (𝓕 (fun x : ℝ => Complex.exp (-((a * |x| : ℝ) : ℂ)) )) w =
      (2 * (a : ℂ)) / ((a : ℂ) ^ 2 + (2 * Real.pi * (w : ℂ)) ^ 2) := by
  let g : ℝ → ℂ := fun x =>
    Complex.exp ((-2 * Real.pi * x * w : ℝ) * I) * Complex.exp (-((a * |x| : ℝ) : ℂ))
  let b : ℂ := (a : ℂ) - 2 * Real.pi * w * I
  let c : ℂ := -(a : ℂ) - 2 * Real.pi * w * I
  have hb : 0 < b.re := by simpa [b] using ha
  have hc : c.re < 0 := by simpa [c] using (neg_neg_of_pos ha)
  have hneg : EqOn (fun x : ℝ => Complex.exp (b * x)) g (Iic 0) := by
    intro x hx
    dsimp [g, b]
    rw [abs_of_nonpos hx, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpos : EqOn (fun x : ℝ => Complex.exp (c * x)) g (Ioi 0) := by
    intro x hx
    dsimp [g, c]
    rw [abs_of_pos hx, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hn := (integrableOn_exp_mul_complex_Iic hb 0).congr_fun hneg measurableSet_Iic
  have hp := (integrableOn_exp_mul_complex_Ioi hc 0).congr_fun hpos measurableSet_Ioi
  rw [fourier_real_eq_integral_exp_smul]
  change (∫ x, g x) = _
  rw [← intervalIntegral.integral_Iic_add_Ioi hn hp,
    ← setIntegral_congr_fun measurableSet_Iic hneg,
    ← setIntegral_congr_fun measurableSet_Ioi hpos,
    integral_exp_mul_complex_Iic hb, integral_exp_mul_complex_Ioi hc]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hd : (a : ℂ) ^ 2 + (2 * Real.pi * (w : ℂ)) ^ 2 ≠ 0 := by
    have h : 0 < a ^ 2 + (2 * Real.pi * w) ^ 2 := by positivity
    exact_mod_cast ne_of_gt h
  dsimp [b, c] at hb0 hc0 ⊢
  apply (eq_div_iff hd).mpr
  field_simp [hb0, hc0]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem signed_laplace_transform (a w : ℝ) (ha : 0 < a) :
    (𝓕 (fun x : ℝ => if x ≤ 0 then Complex.exp (-((a * |x| : ℝ) : ℂ))
      else -Complex.exp (-((a * |x| : ℝ) : ℂ)))) w =
      (2 * (2 * Real.pi * (w : ℂ)) * Complex.I) /
        ((a : ℂ) ^ 2 + (2 * Real.pi * (w : ℂ)) ^ 2) := by
  let g : ℝ → ℂ := fun x => Complex.exp ((-2 * Real.pi * x * w : ℝ) * I) *
    (if x ≤ 0 then Complex.exp (-((a * |x| : ℝ) : ℂ))
      else -Complex.exp (-((a * |x| : ℝ) : ℂ)))
  let b : ℂ := (a : ℂ) - 2 * Real.pi * w * I
  let c : ℂ := -(a : ℂ) - 2 * Real.pi * w * I
  have hb : 0 < b.re := by simpa [b] using ha
  have hc : c.re < 0 := by simpa [c] using (neg_neg_of_pos ha)
  have hneg : EqOn (fun x : ℝ => Complex.exp (b * x)) g (Iic 0) := by
    intro x hx
    dsimp [g, b]
    have hx0 : x ≤ 0 := hx
    rw [if_pos hx0, abs_of_nonpos hx0, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpos : EqOn (fun x : ℝ => -Complex.exp (c * x)) g (Ioi 0) := by
    intro x hx
    dsimp [g, c]
    rw [if_neg (not_le.mpr hx), abs_of_pos hx, mul_neg, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  have hn := (integrableOn_exp_mul_complex_Iic hb 0).congr_fun hneg measurableSet_Iic
  have hp := ((integrableOn_exp_mul_complex_Ioi hc 0).neg).congr_fun hpos measurableSet_Ioi
  rw [fourier_real_eq_integral_exp_smul]
  change (∫ x, g x) = _
  rw [← intervalIntegral.integral_Iic_add_Ioi hn hp,
    ← setIntegral_congr_fun measurableSet_Iic hneg,
    ← setIntegral_congr_fun measurableSet_Ioi hpos,
    integral_neg, integral_exp_mul_complex_Iic hb, integral_exp_mul_complex_Ioi hc]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hd : (a : ℂ) ^ 2 + (2 * Real.pi * (w : ℂ)) ^ 2 ≠ 0 := by
    have h : 0 < a ^ 2 + (2 * Real.pi * w) ^ 2 := by positivity
    exact_mod_cast ne_of_gt h
  dsimp [b, c] at hb0 hc0 ⊢
  apply (eq_div_iff hd).mpr
  field_simp [hb0, hc0]
  ring_nf
  rw [Complex.I_pow_three]
  ring

theorem laplace_kernel_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => Complex.exp (-((a * |x| : ℝ) : ℂ))) := by
  let f : ℝ → ℂ := fun x => Complex.exp (-((a * |x| : ℝ) : ℂ))
  have hfn : IntegrableOn f (Iic 0) := by
    refine (integrableOn_exp_mul_complex_Iic (a := (a : ℂ)) (by simpa using ha) 0).congr_fun
      (fun x hx => ?_) measurableSet_Iic
    simp [f, abs_of_nonpos (show x ≤ 0 from hx)]
  have hfp : IntegrableOn f (Ioi 0) := by
    refine (integrableOn_exp_mul_complex_Ioi (a := -(a : ℂ)) (by simpa using ha) 0).congr_fun
      (fun x hx => ?_) measurableSet_Ioi
    simp [f, abs_of_pos (show 0 < x from hx)]
  have h := hfn.union hfp
  simpa only [Iic_union_Ioi, integrableOn_univ] using h

theorem signed_laplace_kernel_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => if x ≤ 0 then Complex.exp (-((a * |x| : ℝ) : ℂ))
      else -Complex.exp (-((a * |x| : ℝ) : ℂ))) := by
  have hi := laplace_kernel_integrable a ha
  simpa only [Set.piecewise, Set.mem_Iic, Pi.neg_apply] using!
    Integrable.piecewise measurableSet_Iic hi.integrableOn hi.neg.integrableOn


private lemma tanh_sub_one (u : ℝ) :
    Real.tanh u - 1 = -Real.exp (-u) / Real.cosh u := by
  rw [Real.tanh_eq_sinh_div_cosh]
  apply (eq_div_iff (ne_of_gt (Real.cosh_pos u))).mpr
  have h := Real.sinh_sub_cosh u
  field_simp [ne_of_gt (Real.cosh_pos u)]
  linarith

private lemma tanh_add_one (u : ℝ) :
    Real.tanh u + 1 = Real.exp u / Real.cosh u := by
  rw [Real.tanh_eq_sinh_div_cosh]
  apply (eq_div_iff (ne_of_gt (Real.cosh_pos u))).mpr
  have h := Real.sinh_add_cosh u
  field_simp [ne_of_gt (Real.cosh_pos u)]
  linarith

/-- The continuum correction kernel is exactly the negative bound-state
rank-one kernel. The two half-lines agree at the diagonal. -/
theorem reflectionless_correction_kernel (u v : ℝ) :
    Real.exp (-|v - u|) *
      (Real.tanh u * Real.tanh v - 1 -
        (if u ≤ v then Real.tanh v - Real.tanh u else Real.tanh u - Real.tanh v)) =
      -1 / (Real.cosh u * Real.cosh v) := by
  by_cases huv : u ≤ v
  · rw [if_pos huv, abs_of_nonneg (sub_nonneg.mpr huv)]
    rw [show Real.tanh u * Real.tanh v - 1 - (Real.tanh v - Real.tanh u) =
      (Real.tanh u - 1) * (Real.tanh v + 1) by ring, tanh_sub_one, tanh_add_one]
    have he : Real.exp (-(v - u)) * (Real.exp (-u) * Real.exp v) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      rw [show -(v - u) + (-u + v) = 0 by ring, Real.exp_zero]
    field_simp [ne_of_gt (Real.cosh_pos u), ne_of_gt (Real.cosh_pos v)]
    linear_combination -he
  · rw [if_neg huv, abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge huv))]
    rw [show Real.tanh u * Real.tanh v - 1 - (Real.tanh u - Real.tanh v) =
      (Real.tanh u + 1) * (Real.tanh v - 1) by ring, tanh_sub_one, tanh_add_one]
    have he : Real.exp (-(-(v - u))) * (Real.exp u * Real.exp (-v)) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      rw [show -(-(v - u)) + (u + -v) = 0 by ring, Real.exp_zero]
    simp only [neg_neg] at he
    field_simp [ne_of_gt (Real.cosh_pos u), ne_of_gt (Real.cosh_pos v)]
    linear_combination -he

open ReflectionlessPotential

noncomputable def resolventKernel (κ x : ℝ) : ℝ := κ / 2 * Real.exp (-(κ * |x|))
noncomputable def signedResolventKernel (κ x : ℝ) : ℝ :=
  if x ≤ 0 then resolventKernel κ x else -resolventKernel κ x

theorem spatial_correction_rank_one (κ x y : ℝ) (hκ : 0 < κ) :
    resolventKernel κ (x - y) * (Real.tanh (κ * x) * Real.tanh (κ * y) - 1) +
      signedResolventKernel κ (x - y) * (Real.tanh (κ * x) - Real.tanh (κ * y)) =
      -psi0 κ x * psi0 κ y := by
  have hk := reflectionless_correction_kernel (κ * x) (κ * y)
  have hsub : κ * y - κ * x = κ * (y - x) := by ring
  rw [hsub, abs_mul, abs_of_pos hκ] at hk
  have hle : κ * x ≤ κ * y ↔ x ≤ y := mul_le_mul_iff_right₀ hκ
  simp only [hle] at hk
  have hpsi : psi0 κ x * psi0 κ y = (κ / 2) /
      (Real.cosh (κ * x) * Real.cosh (κ * y)) := by
    dsimp [psi0]
    rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt (by positivity : 0 ≤ κ / 2)]
  rw [neg_mul, hpsi]
  calc
    _ = (κ / 2) * (Real.exp (-(κ * |y - x|)) *
        (Real.tanh (κ * x) * Real.tanh (κ * y) - 1 -
          (if x ≤ y then Real.tanh (κ * y) - Real.tanh (κ * x)
            else Real.tanh (κ * x) - Real.tanh (κ * y)))) := by
      dsimp [signedResolventKernel, resolventKernel]
      rw [abs_sub_comm]
      by_cases hxy : x ≤ y
      · rw [if_pos (sub_nonpos.mpr hxy), if_pos hxy]
        ring
      · rw [if_neg (not_le.mpr (sub_pos.mpr (lt_of_not_ge hxy))), if_neg hxy]
        ring
    _ = -(κ / 2 / (Real.cosh (κ * x) * Real.cosh (κ * y))) := by
      rw [hk]
      ring

theorem resolvent_kernel_fourier (κ w : ℝ) (hκ : 0 < κ) :
    (𝓕 (fun x : ℝ => (resolventKernel κ x : ℂ))) w =
      (κ : ℂ) ^ 2 / ((κ : ℂ) ^ 2 + (2 * Real.pi * w) ^ 2) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he (x : ℝ) : Complex.exp (↑(-2 * Real.pi * x * w) * I) *
      (resolventKernel κ x : ℂ) = (κ / 2 : ℂ) *
        (Complex.exp (↑(-2 * Real.pi * x * w) * I) *
          Complex.exp (-((κ * |x| : ℝ) : ℂ))) := by
    dsimp [resolventKernel]
    push_cast
    ring
  change (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * w) * I) *
    (resolventKernel κ x : ℂ)) = _
  simp_rw [he]
  rw [integral_const_mul]
  have ht := laplace_transform κ w hκ
  rw [Real.fourier_real_eq_integral_exp_smul] at ht
  simp only [smul_eq_mul] at ht
  rw [ht]
  ring

theorem signed_resolvent_kernel_fourier (κ w : ℝ) (hκ : 0 < κ) :
    (𝓕 (fun x : ℝ => (signedResolventKernel κ x : ℂ))) w =
      I * κ * (2 * Real.pi * w) / ((κ : ℂ) ^ 2 + (2 * Real.pi * w) ^ 2) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he (x : ℝ) : Complex.exp (↑(-2 * Real.pi * x * w) * I) *
      (signedResolventKernel κ x : ℂ) = (κ / 2 : ℂ) *
        (Complex.exp (↑(-2 * Real.pi * x * w) * I) *
          (if x ≤ 0 then Complex.exp (-((κ * |x| : ℝ) : ℂ))
            else -Complex.exp (-((κ * |x| : ℝ) : ℂ)))) := by
    dsimp [signedResolventKernel, resolventKernel]
    split_ifs <;> push_cast <;> ring
  change (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * w) * I) *
    (signedResolventKernel κ x : ℂ)) = _
  simp_rw [he]
  rw [integral_const_mul]
  have ht := signed_laplace_transform κ w hκ
  rw [Real.fourier_real_eq_integral_exp_smul] at ht
  simp only [smul_eq_mul] at ht
  rw [ht]
  ring

theorem resolvent_kernel_integrable (κ : ℝ) (hκ : 0 < κ) :
    Integrable (fun x : ℝ => (resolventKernel κ x : ℂ)) := by
  convert! (laplace_kernel_integrable κ hκ).const_mul (κ / 2 : ℂ) using 1
  funext x
  dsimp [resolventKernel]
  push_cast
  ring

theorem signed_resolvent_kernel_integrable (κ : ℝ) (hκ : 0 < κ) :
    Integrable (fun x : ℝ => (signedResolventKernel κ x : ℂ)) := by
  convert! (signed_laplace_kernel_integrable κ hκ).const_mul (κ / 2 : ℂ) using 1
  funext x
  dsimp [signedResolventKernel, resolventKernel]
  split_ifs <;> push_cast <;> ring


open ReflectionlessPotential Complex MeasureTheory FourierTransform
open scoped ComplexConjugate

set_option backward.isDefEq.respectTransparency false

theorem continuum_eigenfunction_conjugate (κ k x : ℝ) :
    starRingEnd ℂ (psiC κ k x) =
      Complex.exp (-I * k * x) * ((k : ℂ) - I * κ * Real.tanh (κ * x)) /
        ((Real.sqrt (2 * Real.pi) : ℂ) * ((κ : ℂ) - I * k)) := by
  dsimp [psiC]
  simp only [map_div₀, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I,
    ← Complex.exp_conj, neg_mul, ← sub_eq_add_neg]

private lemma phase_integrable (k : ℝ) (f : ℝ → ℂ) (hf : Integrable f) :
    Integrable (fun x : ℝ => Complex.exp (-I * k * x) * f x) := by
  apply hf.bdd_mul (c := 1) (by fun_prop)
  filter_upwards with x
  simp [Complex.norm_exp, Complex.mul_re]

theorem continuum_coefficient_fourier (κ w : ℝ) (f : ℝ → ℂ) (hf : Integrable f)
    (htf : Integrable (fun x : ℝ => (Real.tanh (κ * x) : ℂ) * f x)) :
    coeffC κ (2 * Real.pi * w) f =
      ((2 * Real.pi * (w : ℂ)) * (𝓕 f) w - I * κ *
        (𝓕 (fun x : ℝ => (Real.tanh (κ * x) : ℂ) * f x)) w) /
        ((Real.sqrt (2 * Real.pi) : ℂ) * ((κ : ℂ) - I * (2 * Real.pi * w))) := by
  let k : ℝ := 2 * Real.pi * w
  let T : ℝ → ℂ := fun x => (Real.tanh (κ * x) : ℂ) * f x
  have hp (x : ℝ) : starRingEnd ℂ (psiC κ k x) * f x =
      ((k : ℂ) * (Complex.exp (-I * k * x) * f x) -
        I * κ * (Complex.exp (-I * k * x) * T x)) /
        ((Real.sqrt (2 * Real.pi) : ℂ) * ((κ : ℂ) - I * k)) := by
    rw [continuum_eigenfunction_conjugate]
    dsimp [T]
    ring
  have hFour (u : ℝ → ℂ) : (∫ x : ℝ, Complex.exp (-I * k * x) * u x) = (𝓕 u) w := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    congr 1
    funext x
    congr 1
    congr 1
    dsimp [k]
    push_cast
    ring
  change (∫ x : ℝ, starRingEnd ℂ (psiC κ k x) * f x) = _
  simp_rw [hp]
  rw [integral_div, integral_sub ((phase_integrable k f hf).const_mul (k : ℂ))
    ((phase_integrable k T htf).const_mul (I * κ)), integral_const_mul, integral_const_mul,
    hFour f, hFour T]
  dsimp [k, T]
  push_cast
  rfl


open Complex

set_option backward.isDefEq.respectTransparency false

theorem continuum_norm_expansion (κ k : ℝ) (hκ : 0 < κ) (F G : ℂ) :
    ‖((k : ℂ) * F - I * κ * G) / ((κ : ℂ) - I * k)‖ ^ 2 = ‖F‖ ^ 2 +
      (star G * (((κ : ℂ) ^ 2 / ((κ : ℂ) ^ 2 + k ^ 2)) * G) -
       star F * (((κ : ℂ) ^ 2 / ((κ : ℂ) ^ 2 + k ^ 2)) * F) -
       star F * ((I * κ * k / ((κ : ℂ) ^ 2 + k ^ 2)) * G) +
       star G * ((I * κ * k / ((κ : ℂ) ^ 2 + k ^ 2)) * F)).re := by
  have hd : 0 < κ ^ 2 + k ^ 2 := by positivity
  have hn : ‖((κ : ℂ) - I * k)‖ ^ 2 = κ ^ 2 + k ^ 2 := by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hcast : ((κ : ℂ) ^ 2 + k ^ 2) = ((κ ^ 2 + k ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_pow]
  rw [norm_div, div_pow, hn, hcast]
  simp_rw [Complex.sq_norm]
  simp only [div_eq_mul_inv, Complex.normSq_apply, pow_two,
    mul_re, mul_im, sub_re, sub_im, add_re, conj_re, conj_im, ofReal_re, ofReal_im,
    I_re, I_im, inv_re, inv_im, zero_mul, mul_zero, one_mul,
    sub_zero, add_zero, zero_sub, neg_zero, star_def]
  field_simp [ne_of_gt hd]
  ring

open MeasureTheory ContinuousLinearMap FourierTransform
open scoped Convolution

theorem integral_four_terms (a b c d : ℝ → ℂ)
    (ha : Integrable a) (hb : Integrable b) (hc : Integrable c) (hd : Integrable d) :
    (∫ x : ℝ, a x - b x - c x + d x) =
      (∫ x : ℝ, a x) - (∫ x : ℝ, b x) - (∫ x : ℝ, c x) + (∫ x : ℝ, d x) := by
  have h1 : (∫ x : ℝ, a x - b x) = (∫ x : ℝ, a x) - (∫ x : ℝ, b x) := by
    simpa only [Pi.sub_apply] using! integral_sub ha hb
  have h2 : (∫ x : ℝ, a x - b x - c x) = (∫ x : ℝ, a x - b x) - (∫ x : ℝ, c x) := by
    simpa only [Pi.sub_apply] using! integral_sub (ha.sub hb) hc
  have h3 : (∫ x : ℝ, a x - b x - c x + d x) =
      (∫ x : ℝ, a x - b x - c x) + (∫ x : ℝ, d x) := by
    simpa only [Pi.sub_apply, Pi.add_apply] using! integral_add ((ha.sub hb).sub hc) hd
  rw [h3, h2, h1]

theorem multiplier_kernel_pairing (a f g : ℝ → ℂ)
    (ha : Integrable a) (hf : Integrable f) (hg : Integrable g)
    (hc : Continuous f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C)
    (hg2 : MemLp g 2 volume) :
    ∫ x : ℝ, star ((𝓕 g) x) * ((𝓕 a) x * (𝓕 f) x) =
      ∫ x : ℝ, ∫ y : ℝ, star (g x) * a (x - y) * f y := by
  rw [multiplier_convolution_pairing a f g ha hf hg hc C hb hg2]
  apply integral_congr_ae
  filter_upwards with x
  rw [convolution_eq_swap]
  change star (g x) * (∫ y : ℝ, a (x - y) * f y) = _
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

theorem multiplier_kernel_pair_integrable (a f g : ℝ → ℂ)
    (ha : Integrable a) (hf : Integrable f) (hg : Integrable g)
    (hc : Continuous f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C)
    (hg2 : MemLp g 2 volume) :
    Integrable (fun x : ℝ => star ((𝓕 g) x) * ((𝓕 a) x * (𝓕 f) x)) := by
  have hcv := ha.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf
  have hc2 := convolution_integrable_bounded_memLp a f ha hf hc C hb
  have hF := fourier_integral_memLp (a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) hcv hc2
  have hi := (fourier_integral_memLp g hg hg2).star.integrable_mul hF
  convert! hi using 1
  funext x
  change star ((𝓕 g) x) * ((𝓕 a) x * (𝓕 f) x) =
    star ((𝓕 g) x) * (𝓕 (a ⋆[ContinuousLinearMap.mul ℂ ℂ] f)) x
  rw [Real.fourier_mul_convolution_eq ha hf]

theorem tanh_product_bound (κ : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    ‖(Real.tanh (κ * x) : ℂ) * f x‖ ≤ ‖f x‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (Real.abs_tanh_lt_one _).le (norm_nonneg _)).trans_eq
    (one_mul _)

theorem kernel_pair_integrable (a f g : ℝ → ℂ)
    (ha : Integrable a) (hf : Integrable f)
    (hc : Continuous f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C)
    (hg2 : MemLp g 2 volume) :
    Integrable (fun x : ℝ => ∫ y : ℝ, star (g x) * a (x - y) * f y) := by
  have hc2 := convolution_integrable_bounded_memLp a f ha hf hc C hb
  have hi := hg2.star.integrable_mul hc2
  convert! hi using 1
  funext x
  change (∫ y : ℝ, star (g x) * a (x - y) * f y) =
    star (g x) * (a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x
  rw [convolution_eq_swap]
  change (∫ y : ℝ, star (g x) * a (x - y) * f y) =
    star (g x) * (∫ y : ℝ, a (x - y) * f y)
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

theorem kernel_row_integrable (a f : ℝ → ℂ) (z : ℂ) (x : ℝ)
    (ha : Integrable a) (hc : Continuous f) (C : ℝ) (hb : ∀ y, ‖f y‖ ≤ C) :
    Integrable (fun y : ℝ => z * a (x - y) * f y) := by
  have hi := (ha.comp_sub_left x).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  simpa only [mul_assoc] using! hi.const_mul z

theorem bound_projection_iterated_integral (κ : ℝ) (f : ℝ → ℂ) :
    (∫ x : ℝ, ∫ y : ℝ, star (f x) * f y *
      (-(psi0 κ x : ℂ) * (psi0 κ y : ℂ))) = -(‖coeff0 κ f‖ ^ 2 : ℝ) := by
  have hr (x : ℝ) : (∫ y : ℝ, star (f x) * f y *
      (-(psi0 κ x : ℂ) * (psi0 κ y : ℂ))) =
      -conj ((psi0 κ x : ℂ) * f x) * coeff0 κ f := by
    change _ = -conj ((psi0 κ x : ℂ) * f x) * (∫ y : ℝ, (psi0 κ y : ℂ) * f y)
    rw [← integral_const_mul]
    congr 1
    funext y
    simp only [map_mul, Complex.conj_ofReal, star_def]
    ring
  simp_rw [hr]
  rw [integral_mul_const, integral_neg, integral_conj]
  change -(conj (coeff0 κ f)) * coeff0 κ f = _
  rw [neg_mul, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]


theorem spatial_four_pairings (κ : ℝ) (hκ : 0 < κ) (f : ℝ → ℂ)
    (hf : Integrable f) (hc : Continuous f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    let T : ℝ → ℂ := fun x => (Real.tanh (κ * x) : ℂ) * f x
    let Q : ℝ → ℂ := fun x => (resolventKernel κ x : ℂ)
    let S : ℝ → ℂ := fun x => (signedResolventKernel κ x : ℂ)
    (∫ x : ℝ, ∫ y : ℝ, star (T x) * Q (x - y) * T y) -
      (∫ x : ℝ, ∫ y : ℝ, star (f x) * Q (x - y) * f y) -
      (∫ x : ℝ, ∫ y : ℝ, star (f x) * S (x - y) * T y) +
      (∫ x : ℝ, ∫ y : ℝ, star (T x) * S (x - y) * f y) = -(‖coeff0 κ f‖ ^ 2 : ℝ) := by
  let T : ℝ → ℂ := fun x => (Real.tanh (κ * x) : ℂ) * f x
  let Q : ℝ → ℂ := fun x => (resolventKernel κ x : ℂ)
  let S : ℝ → ℂ := fun x => (signedResolventKernel κ x : ℂ)
  let H (a u v : ℝ → ℂ) (x : ℝ) : ℂ := ∫ y : ℝ, star (u x) * a (x - y) * v y
  change (∫ x : ℝ, H Q T T x) - (∫ x : ℝ, H Q f f x) -
    (∫ x : ℝ, H S f T x) + (∫ x : ℝ, H S T f x) = _
  have hcTan : Continuous (fun x : ℝ => (Real.tanh (κ * x) : ℂ)) := by
    have ht : Continuous Real.tanh := by
      rw [show Real.tanh = (fun x : ℝ => Real.sinh x / Real.cosh x) from
        funext Real.tanh_eq_sinh_div_cosh]
      exact Real.continuous_sinh.div Real.continuous_cosh
        (fun x => ne_of_gt (Real.cosh_pos x))
    exact Complex.continuous_ofReal.comp (ht.comp (continuous_const.mul continuous_id))
  have hcT : Continuous T := hcTan.mul hc
  have hbT (x : ℝ) : ‖T x‖ ≤ C := (tanh_product_bound κ f x).trans (hb x)
  have hiT : Integrable T := by
    apply hf.bdd_mul (c := 1) hcTan.aestronglyMeasurable
    filter_upwards with x
    simpa only [Complex.norm_real, Real.norm_eq_abs] using (Real.abs_tanh_lt_one (κ * x)).le
  have hf2 := integrable_bounded_memLp_two f hf C hb
  have hT2 := integrable_bounded_memLp_two T hiT C hbT
  have hQ := resolvent_kernel_integrable κ hκ
  have hS := signed_resolvent_kernel_integrable κ hκ
  have h1 := kernel_pair_integrable Q T T hQ hiT hcT C hbT hT2
  have h2 := kernel_pair_integrable Q f f hQ hf hc C hb hf2
  have h3 := kernel_pair_integrable S T f hS hiT hcT C hbT hf2
  have h4 := kernel_pair_integrable S f T hS hf hc C hb hT2
  have hp (x : ℝ) : H Q T T x - H Q f f x - H S f T x + H S T f x =
      ∫ y : ℝ, star (f x) * f y * (-(psi0 κ x : ℂ) * (psi0 κ y : ℂ)) := by
    have h1x := kernel_row_integrable Q T (star (T x)) x hQ hcT C hbT
    have h2x := kernel_row_integrable Q f (star (f x)) x hQ hc C hb
    have h3x := kernel_row_integrable S T (star (f x)) x hS hcT C hbT
    have h4x := kernel_row_integrable S f (star (T x)) x hS hc C hb
    have hiEq := integral_four_terms _ _ _ _ h1x h2x h3x h4x
    change (∫ y : ℝ, star (T x) * Q (x - y) * T y - star (f x) * Q (x - y) * f y -
      star (f x) * S (x - y) * T y + star (T x) * S (x - y) * f y) =
      H Q T T x - H Q f f x - H S f T x + H S T f x at hiEq
    rw [← hiEq]
    apply integral_congr_ae
    filter_upwards with y
    have hk := congrArg (fun r : ℝ => (r : ℂ)) (spatial_correction_rank_one κ x y hκ)
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_neg] at hk
    dsimp [T, Q, S]
    simp only [map_mul, Complex.conj_ofReal]
    linear_combination conj (f x) * f y * hk
  have h1' : Integrable (H Q T T) := h1
  have h2' : Integrable (H Q f f) := h2
  have h3' : Integrable (H S f T) := h3
  have h4' : Integrable (H S T f) := h4
  have ho := integral_four_terms _ _ _ _ h1' h2' h3' h4'
  change (∫ x : ℝ, H Q T T x - H Q f f x - H S f T x + H S T f x) = _ at ho
  rw [← ho]
  simp_rw [hp]
  exact bound_projection_iterated_integral κ f


set_option maxHeartbeats 1200000

theorem normalized_continuum_completeness (κ : ℝ) (hκ : 0 < κ) (f : ℝ → ℂ)
    (hf : Integrable f) (hc : Continuous f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    let T : ℝ → ℂ := fun x => (Real.tanh (κ * x) : ℂ) * f x
    (∫ w : ℝ, ‖((2 * Real.pi * (w : ℂ)) * (𝓕 f) w - I * κ * (𝓕 T) w) /
      ((κ : ℂ) - I * (2 * Real.pi * w))‖ ^ 2) + ‖coeff0 κ f‖ ^ 2 =
      ∫ x : ℝ, ‖f x‖ ^ 2 := by
  let T : ℝ → ℂ := fun x => (Real.tanh (κ * x) : ℂ) * f x
  let Q : ℝ → ℂ := fun x => (resolventKernel κ x : ℂ)
  let S : ℝ → ℂ := fun x => (signedResolventKernel κ x : ℂ)
  let N (a u v : ℝ → ℂ) (w : ℝ) : ℂ := star ((𝓕 u) w) * ((𝓕 a) w * (𝓕 v) w)
  let D : ℝ → ℂ := fun w => N Q T T w - N Q f f w - N S f T w + N S T f w
  have hcTan : Continuous (fun x : ℝ => (Real.tanh (κ * x) : ℂ)) := by
    have ht : Continuous Real.tanh := by
      rw [show Real.tanh = (fun x : ℝ => Real.sinh x / Real.cosh x) from
        funext Real.tanh_eq_sinh_div_cosh]
      exact Real.continuous_sinh.div Real.continuous_cosh
        (fun x => ne_of_gt (Real.cosh_pos x))
    exact Complex.continuous_ofReal.comp (ht.comp (continuous_const.mul continuous_id))
  have hcT : Continuous T := hcTan.mul hc
  have hbT (x : ℝ) : ‖T x‖ ≤ C := (tanh_product_bound κ f x).trans (hb x)
  have hiT : Integrable T := by
    apply hf.bdd_mul (c := 1) hcTan.aestronglyMeasurable
    filter_upwards with x
    simpa only [Complex.norm_real, Real.norm_eq_abs] using (Real.abs_tanh_lt_one (κ * x)).le
  have hf2 := integrable_bounded_memLp_two f hf C hb
  have hT2 := integrable_bounded_memLp_two T hiT C hbT
  have hQ := resolvent_kernel_integrable κ hκ
  have hS := signed_resolvent_kernel_integrable κ hκ
  have h1 : Integrable (N Q T T) := multiplier_kernel_pair_integrable Q T T hQ hiT hiT hcT C hbT hT2
  have h2 : Integrable (N Q f f) := multiplier_kernel_pair_integrable Q f f hQ hf hf hc C hb hf2
  have h3 : Integrable (N S f T) := multiplier_kernel_pair_integrable S T f hS hiT hf hcT C hbT hf2
  have h4 : Integrable (N S T f) := multiplier_kernel_pair_integrable S f T hS hf hiT hc C hb hT2
  have hD : Integrable D := ((h1.sub h2).sub h3).add h4
  have hDI : (∫ w : ℝ, D w) = -(‖coeff0 κ f‖ ^ 2 : ℝ) := by
    have ho := integral_four_terms _ _ _ _ h1 h2 h3 h4
    change (∫ w : ℝ, D w) = _ at ho
    rw [ho]
    change (∫ w : ℝ, star ((𝓕 T) w) * ((𝓕 Q) w * (𝓕 T) w)) -
      (∫ w : ℝ, star ((𝓕 f) w) * ((𝓕 Q) w * (𝓕 f) w)) -
      (∫ w : ℝ, star ((𝓕 f) w) * ((𝓕 S) w * (𝓕 T) w)) +
      (∫ w : ℝ, star ((𝓕 T) w) * ((𝓕 S) w * (𝓕 f) w)) = _
    rw [multiplier_kernel_pairing Q T T hQ hiT hiT hcT C hbT hT2,
      multiplier_kernel_pairing Q f f hQ hf hf hc C hb hf2,
      multiplier_kernel_pairing S T f hS hiT hf hcT C hbT hf2,
      multiplier_kernel_pairing S f T hS hf hiT hc C hb hT2]
    exact spatial_four_pairings κ hκ f hf hc C hb
  have hp (w : ℝ) : ‖((2 * Real.pi * (w : ℂ)) * (𝓕 f) w - I * κ * (𝓕 T) w) /
      ((κ : ℂ) - I * (2 * Real.pi * w))‖ ^ 2 = ‖(𝓕 f) w‖ ^ 2 + (D w).re := by
    have h := continuum_norm_expansion κ (2 * Real.pi * w) hκ ((𝓕 f) w) ((𝓕 T) w)
    have hw : ((2 * Real.pi * w : ℝ) : ℂ) = 2 * Real.pi * (w : ℂ) := by push_cast; rfl
    rw [hw] at h
    rw [← resolvent_kernel_fourier κ w hκ, ← signed_resolvent_kernel_fourier κ w hκ] at h
    exact h
  have hNorm : Integrable (fun w : ℝ => ‖(𝓕 f) w‖ ^ 2) :=
    (fourier_integral_memLp f hf hf2).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hDRe : Integrable (fun w : ℝ => (D w).re) := by simpa only using! hD.re
  have hsplit : (∫ w : ℝ, ‖(𝓕 f) w‖ ^ 2 + (D w).re) =
      (∫ w : ℝ, ‖(𝓕 f) w‖ ^ 2) + (∫ w : ℝ, (D w).re) := by
    simpa only using! integral_add hNorm hDRe
  have hreal : (∫ w : ℝ, (D w).re) = (∫ w : ℝ, D w).re := by
    simpa only using! integral_re hD
  change (∫ w : ℝ, ‖((2 * Real.pi * (w : ℂ)) * (𝓕 f) w - I * κ * (𝓕 T) w) /
    ((κ : ℂ) - I * (2 * Real.pi * w))‖ ^ 2) + _ = _
  simp_rw [hp]
  rw [hsplit, hreal, hDI]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rw [add_assoc, neg_add_cancel, add_zero, fourier_integral_norm_sq f hf hf2]


set_option maxHeartbeats 1200000

theorem solution (κ : ℝ) (hκ : 0 < κ) (f : ℝ → ℂ)
    (hf : Continuous f) (hsupp : HasCompactSupport f) :
    (∫ k : ℝ, ‖coeffC κ k f‖ ^ 2) + ‖coeff0 κ f‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  have hi : Integrable f volume := hf.integrable_of_hasCompactSupport hsupp
  obtain ⟨x0, hb⟩ := hf.norm.exists_forall_ge_of_hasCompactSupport hsupp.norm
  let C : ℝ := ‖f x0‖
  have hb' (x : ℝ) : ‖f x‖ ≤ C := hb x
  let T : ℝ → ℂ := fun x => (Real.tanh (κ * x) : ℂ) * f x
  have hcTan : Continuous (fun x : ℝ => (Real.tanh (κ * x) : ℂ)) := by
    have ht : Continuous Real.tanh := by
      rw [show Real.tanh = (fun x : ℝ => Real.sinh x / Real.cosh x) from
        funext Real.tanh_eq_sinh_div_cosh]
      exact Real.continuous_sinh.div Real.continuous_cosh
        (fun x => ne_of_gt (Real.cosh_pos x))
    exact Complex.continuous_ofReal.comp (ht.comp (continuous_const.mul continuous_id))
  have hiT : Integrable T := by
    apply hi.bdd_mul (c := 1) hcTan.aestronglyMeasurable
    filter_upwards with x
    simpa only [Complex.norm_real, Real.norm_eq_abs] using (Real.abs_tanh_lt_one (κ * x)).le
  let R (w : ℝ) : ℂ := ((2 * Real.pi * (w : ℂ)) * (𝓕 f) w - I * κ * (𝓕 T) w) /
    ((κ : ℂ) - I * (2 * Real.pi * w))
  have hs : ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ ^ 2 = 2 * Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
  have hcf (w : ℝ) : coeffC κ (2 * Real.pi * w) f = R w / (Real.sqrt (2 * Real.pi) : ℂ) := by
    rw [continuum_coefficient_fourier κ w f hi hiT]
    dsimp [R]
    rw [div_div]
    congr 1
    ring
  have hn (w : ℝ) : 2 * Real.pi * ‖coeffC κ (2 * Real.pi * w) f‖ ^ 2 = ‖R w‖ ^ 2 := by
    rw [hcf w, norm_div, div_pow, hs]
    field_simp
  have hscale : (2 * Real.pi) * (∫ w : ℝ, ‖coeffC κ (2 * Real.pi * w) f‖ ^ 2) =
      ∫ k : ℝ, ‖coeffC κ k f‖ ^ 2 := by
    rw [Measure.integral_comp_mul_left (fun k : ℝ => ‖coeffC κ k f‖ ^ 2) (2 * Real.pi),
      smul_eq_mul, abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)]
    field_simp
  have hRI : (∫ w : ℝ, ‖R w‖ ^ 2) = ∫ k : ℝ, ‖coeffC κ k f‖ ^ 2 := by
    calc
      (∫ w : ℝ, ‖R w‖ ^ 2) = ∫ w : ℝ, 2 * Real.pi * ‖coeffC κ (2 * Real.pi * w) f‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with w
        exact (hn w).symm
      _ = (2 * Real.pi) * (∫ w : ℝ, ‖coeffC κ (2 * Real.pi * w) f‖ ^ 2) :=
        integral_const_mul _ _
      _ = _ := hscale
  have hm := normalized_continuum_completeness κ hκ f hi hf C hb'
  change (∫ w : ℝ, ‖R w‖ ^ 2) + ‖coeff0 κ f‖ ^ 2 = _ at hm
  rw [hRI] at hm
  exact hm

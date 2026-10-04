-- Prove2me | solution 1 for ReflectionlessPotential.bound_state_unique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T10:24:27.835004+00:00
-- url     : https://prove2.me/submissions/26cb1472-0f4f-4e57-9526-d14866870554

import Definitions.Def_ReflectionlessPotentialDefs
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Basic

open Complex Filter MeasureTheory Set Topology

theorem l2_no_eventual_positive_lower_bound (f : ℝ → ℂ) (hf : MemLp f 2 volume)
    (c : ℝ) (hc : 0 < c) (h : ∀ᶠ x : ℝ in atTop, c ≤ ‖f x‖) : False := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 h
  have hi : Integrable (fun x : ℝ => ‖f x‖ ^ 2) := hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hconst : IntegrableOn (fun _ : ℝ => c ^ 2) (Ici X) := by
    apply hi.integrableOn.mono' (aestronglyMeasurable_const)
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg c)] using
      pow_le_pow_left₀ (le_of_lt hc) (hX x hx) 2
  have hh := (integrableOn_const_iff (C := c ^ 2)).mp hconst
  have hz : c = 0 := by simpa using hh
  exact hc.ne' hz

theorem l2_scaled_limit_eq_zero (f : ℝ → ℂ) (hf : MemLp f 2 volume)
    (a : ℝ) (ha : 0 ≤ a) (L : ℂ)
    (hl : Tendsto (fun x : ℝ => (Real.exp (-a * x) : ℂ) * f x) atTop (𝓝 L)) : L = 0 := by
  by_contra hL
  have hc : 0 < ‖L‖ / 2 := by positivity
  have hlimnorm : Tendsto (fun x : ℝ => ‖(Real.exp (-a * x) : ℂ) * f x‖)
      atTop (𝓝 ‖L‖) := hl.norm
  have hb : ∀ᶠ x : ℝ in atTop, ‖L‖ / 2 ≤ ‖f x‖ := by
    filter_upwards [hlimnorm.eventually (Ioi_mem_nhds (by linarith : ‖L‖ / 2 < ‖L‖)),
      eventually_ge_atTop (0 : ℝ)] with x hx hx0
    have he : Real.exp (-a * x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hx0)
    have hn : ‖(Real.exp (-a * x) : ℂ) * f x‖ ≤ ‖f x‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq (one_mul _)
    exact hx.le.trans hn
  exact l2_no_eventual_positive_lower_bound f hf (‖L‖ / 2) hc hb


open Complex

set_option backward.isDefEq.respectTransparency false

theorem linear_ode_exp_solution (c : ℝ) (f : ℝ → ℂ)
    (hf : ∀ x, HasDerivAt f ((c : ℂ) * f x) x) (x : ℝ) :
    f x = f 0 * Complex.exp ((c : ℂ) * x) := by
  let F : ℝ → ℂ := fun t => Complex.exp (-(c : ℂ) * t) * f t
  have hF (t : ℝ) : HasDerivAt F 0 t := by
    have he := (((hasDerivAt_id (t : ℂ)).const_mul (-(c : ℂ))).cexp.comp_ofReal)
    have h := he.mul (hf t)
    have hd : HasDerivAt F
        (Complex.exp (-(c : ℂ) * t) * (-(c : ℂ)) * f t +
          Complex.exp (-(c : ℂ) * t) * ((c : ℂ) * f t)) t := by
      simpa only [F, id_eq, mul_one, Pi.mul_apply] using! h
    convert! hd using 1
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hF t).differentiableAt)
    (fun t => (hF t).deriv) x 0
  have heq : Complex.exp (-(c : ℂ) * x) * f x = f 0 := by simpa [F] using hconst
  calc
    f x = Complex.exp ((c : ℂ) * x) * (Complex.exp (-(c : ℂ) * x) * f x) := by
      rw [← mul_assoc, ← Complex.exp_add]
      simp
    _ = f 0 * Complex.exp ((c : ℂ) * x) := by rw [heq]; ring

theorem free_negative_ode_classification (l : ℝ) (hl : 0 < l) (g h : ℝ → ℂ)
    (hg : ∀ x, HasDerivAt g (h x) x)
    (hh : ∀ x, HasDerivAt h ((l : ℂ) ^ 2 * g x) x) :
    ∃ A B : ℂ, ∀ x : ℝ,
      g x = A * Complex.exp ((l : ℂ) * x) + B * Complex.exp (-(l : ℂ) * x) ∧
      h x = (l : ℂ) * A * Complex.exp ((l : ℂ) * x) -
        (l : ℂ) * B * Complex.exp (-(l : ℂ) * x) := by
  let u : ℝ → ℂ := fun x => h x + (l : ℂ) * g x
  let v : ℝ → ℂ := fun x => h x - (l : ℂ) * g x
  have hu (x : ℝ) : HasDerivAt u ((l : ℂ) * u x) x := by
    convert! (hh x).add ((hg x).const_mul (l : ℂ)) using 1
    dsimp [u]
    ring
  have hv (x : ℝ) : HasDerivAt v ((-l : ℝ) * v x) x := by
    convert! (hh x).sub ((hg x).const_mul (l : ℂ)) using 1
    dsimp [v]
    push_cast
    ring
  have hue (x : ℝ) := linear_ode_exp_solution l u hu x
  have hve (x : ℝ) := linear_ode_exp_solution (-l) v hv x
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  refine ⟨u 0 / (2 * l), -v 0 / (2 * l), fun x => ?_⟩
  have hve' : v x = v 0 * Complex.exp (-(l : ℂ) * x) := by simpa using hve x
  have hg' : 2 * (l : ℂ) * g x = u x - v x := by dsimp [u, v]; ring
  have hh' : 2 * h x = u x + v x := by dsimp [u, v]; ring
  rw [hue x, hve'] at hg' hh'
  simp only [neg_mul] at hg' hh'
  constructor
  · field_simp [hl0]
    linear_combination hg'
  · field_simp [hl0]
    linear_combination hh'


open Complex

set_option backward.isDefEq.respectTransparency false

private noncomputable def aa (κ x : ℝ) : ℝ := κ * Real.tanh (κ * x)
private noncomputable def qq (κ x : ℝ) : ℝ := κ ^ 2 / Real.cosh (κ * x) ^ 2

private lemma aa_deriv (κ x : ℝ) : HasDerivAt (aa κ) (qq κ x) x := by
  have hs := (Real.hasDerivAt_sinh (κ * x)).comp x ((hasDerivAt_id x).const_mul κ)
  have hc := (Real.hasDerivAt_cosh (κ * x)).comp x ((hasDerivAt_id x).const_mul κ)
  have hn : Real.cosh (κ * x) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hd := (hs.div hc hn).const_mul κ
  simp only [mul_one, Function.comp_apply, Pi.div_apply] at hd
  convert! hd using 1
  · funext t
    exact congrArg (κ * ·) (Real.tanh_eq_sinh_div_cosh _)
  · dsimp [qq]
    field_simp [hn]
    nlinarith [congrArg (fun r : ℝ => κ ^ 2 * r) (Real.cosh_sq_sub_sinh_sq (κ * x))]

private lemma qq_deriv (κ x : ℝ) : HasDerivAt (qq κ) (-2 * aa κ x * qq κ x) x := by
  have hc := (Real.hasDerivAt_cosh (κ * x)).comp x ((hasDerivAt_id x).const_mul κ)
  have hn : Real.cosh (κ * x) ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt (Real.cosh_pos _))
  have hd := (hasDerivAt_const x (κ ^ 2)).div (hc.pow 2) hn
  simp only [mul_one] at hd
  convert! hd using 1
  · dsimp [qq, aa]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [ne_of_gt (Real.cosh_pos (κ * x))]
    ring

private lemma aa_qq (κ x : ℝ) : aa κ x ^ 2 + qq κ x = κ ^ 2 := by
  dsimp [aa, qq]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [ne_of_gt (Real.cosh_pos (κ * x))]
  nlinarith [congrArg (fun r : ℝ => κ ^ 2 * r) (Real.cosh_sq_sub_sinh_sq (κ * x))]

/-- The Darboux transformation and its algebraic inverse, proved from the
classical derivative hypotheses without adding an L² assumption on f′. -/
theorem darboux_free_equation (κ l : ℝ) (f f' : ℝ → ℂ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (((l : ℂ) ^ 2 - 2 * qq κ x) * f x) x) :
    ∃ g h : ℝ → ℂ,
      (∀ x, HasDerivAt g (h x) x) ∧
      (∀ x, HasDerivAt h ((l : ℂ) ^ 2 * g x) x) ∧
      (∀ x, g x = f' x + (aa κ x : ℂ) * f x) ∧
      (∀ x, h x - (aa κ x : ℂ) * g x = ((l : ℂ) ^ 2 - κ ^ 2) * f x) := by
  let g : ℝ → ℂ := fun x => f' x + (aa κ x : ℂ) * f x
  let h : ℝ → ℂ := fun x => ((l : ℂ) ^ 2 - qq κ x) * f x + (aa κ x : ℂ) * f' x
  have hda (x : ℝ) := (aa_deriv κ x).ofReal_comp
  have hdq (x : ℝ) := (qq_deriv κ x).ofReal_comp
  refine ⟨g, h, ?_, ?_, fun _ => rfl, ?_⟩
  · intro x
    convert! (hf' x).add ((hda x).mul (hf x)) using 1
    dsimp [g, h]
    ring
  · intro x
    have hd := ((hdq x).const_sub ((l : ℂ) ^ 2)).mul (hf x) |>.add ((hda x).mul (hf' x))
    convert! hd using 1
    dsimp [g, h]
    push_cast
    ring
  · intro x
    have he : (aa κ x : ℂ) ^ 2 + (qq κ x : ℂ) = (κ : ℂ) ^ 2 := by
      exact_mod_cast aa_qq κ x
    dsimp [g, h]
    linear_combination -(f x) * he


open Complex Filter Topology

set_option backward.isDefEq.respectTransparency false

private lemma tanh_exp_ratio (t : ℝ) :
    Real.tanh t = (1 - Real.exp (-2 * t)) / (1 + Real.exp (-2 * t)) := by
  rw [Real.tanh_eq, show -2 * t = -t + -t by ring, Real.exp_add, Real.exp_neg]
  field_simp

theorem exp_decay_limit (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => Real.exp (-a * x)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, id_eq, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).const_mul_atTop ha)

theorem tanh_scaled_limit (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun x : ℝ => Real.tanh (κ * x)) atTop (𝓝 1) := by
  have he : Tendsto (fun x : ℝ => Real.exp (-2 * (κ * x))) atTop (𝓝 0) := by
    convert exp_decay_limit (2 * κ) (by positivity) using 1
    funext x
    congr 1
    ring
  have hq := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub he).div
    (tendsto_const_nhds.add he) (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have hq' : Tendsto (fun x : ℝ => (1 - Real.exp (-2 * (κ * x))) /
      (1 + Real.exp (-2 * (κ * x)))) atTop (𝓝 1) := by
    convert! hq using 1
    simp
  exact hq'.congr (fun x => (tanh_exp_ratio (κ * x)).symm)

theorem linear_exp_decay_limit (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => x * Real.exp (-a * x)) atTop (𝓝 0) := by
  have hh := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    ((tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).const_mul_atTop ha)
  have hd := hh.div_const a
  convert hd using 1
  · funext x
    simp only [Function.comp_apply, id_eq, pow_one]
    rw [show -(a * x) = -a * x by ring]
    field_simp
  · simp

private noncomputable def primitiveCoshSq (κ x : ℝ) : ℝ :=
  x / 2 + Real.sinh (2 * (κ * x)) / (4 * κ)

private lemma primitiveCoshSq_deriv (κ x : ℝ) (hκ : κ ≠ 0) :
    HasDerivAt (primitiveCoshSq κ) (Real.cosh (κ * x) ^ 2) x := by
  have hs := (Real.hasDerivAt_sinh (2 * (κ * x))).comp x
    (((hasDerivAt_id x).const_mul κ).const_mul 2)
  have hd := ((hasDerivAt_id x).div_const 2).add (hs.div_const (4 * κ))
  simp only [id_eq, mul_one, Function.comp_apply] at hd
  have he : (1 : ℝ) / 2 + Real.cosh (2 * (κ * x)) * (2 * κ) / (4 * κ) =
      Real.cosh (κ * x) ^ 2 := by
    rw [Real.cosh_two_mul]
    field_simp [hκ]
    nlinarith [Real.cosh_sq_sub_sinh_sq (κ * x)]
  simpa only [primitiveCoshSq, he] using! hd

theorem resonant_scaled_limit (κ : ℝ) (hκ : 0 < κ) (D C : ℂ) :
    Tendsto (fun x : ℝ => (Real.exp (-κ * x) : ℂ) *
      ((D + C * primitiveCoshSq κ x) / (Real.cosh (κ * x) : ℂ)))
      atTop (𝓝 (C / (4 * κ))) := by
  let e : ℝ → ℝ := fun x => Real.exp (-2 * (κ * x))
  let v : ℝ → ℝ := fun x => x * e x
  let z : ℝ → ℝ := fun x => Real.exp (-4 * (κ * x))
  have he : Tendsto e atTop (𝓝 0) := by
    simpa [e, mul_assoc, neg_mul] using exp_decay_limit (2 * κ) (by positivity)
  have hv : Tendsto v atTop (𝓝 0) := by
    simpa [v, e, mul_assoc, neg_mul] using linear_exp_decay_limit (2 * κ) (by positivity)
  have hz : Tendsto z atTop (𝓝 0) := by
    simpa [z, mul_assoc, neg_mul] using exp_decay_limit (4 * κ) (by positivity)
  have hn := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => D) atTop (𝓝 D)).mul he.ofReal).add
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => C) atTop (𝓝 C)).mul
      ((hv.ofReal.div_const (2 : ℂ)).add
        (((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℂ)) atTop (𝓝 1)).sub hz.ofReal).div_const (8 * (κ : ℂ)))))
  have hd : Tendsto (fun x : ℝ => ((1 : ℂ) + e x) / 2) atTop (𝓝 (1 / 2 : ℂ)) :=
    by simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℂ)) atTop
      (𝓝 1)).add he.ofReal).div_const 2
  have hr := hn.div hd (by norm_num : (1 / 2 : ℂ) ≠ 0)
  simp only [Complex.ofReal_zero] at hr
  have hl : (D * (0 : ℂ) + C * (0 / 2 + (1 - 0) / (8 * κ))) / (1 / 2 : ℂ) =
      C / (4 * κ) := by ring
  rw [hl] at hr
  apply hr.congr
  intro x
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hu0 : ((Real.exp (κ * x) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero (κ * x)
  have hu2 : Real.exp (2 * (κ * x)) = Real.exp (κ * x) ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  have hu4 : Real.exp (4 * (κ * x)) = Real.exp (κ * x) ^ 4 := by
    rw [show 4 * (κ * x) = 2 * (κ * x) + 2 * (κ * x) by ring, Real.exp_add, hu2]
    ring
  have hus : (((Real.exp (κ * x)) ^ 2 + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (by positivity : 0 < Real.exp (κ * x) ^ 2 + 1)
  dsimp [e, v, z, primitiveCoshSq]
  rw [Real.cosh_eq, Real.sinh_eq]
  simp_rw [show -2 * (κ * x) = -(2 * (κ * x)) by ring,
    show -4 * (κ * x) = -(4 * (κ * x)) by ring, Real.exp_neg, hu2, hu4]
  push_cast
  simp only [neg_mul, Complex.exp_neg]
  field_simp [hκ0, hu0, hus, Complex.exp_ne_zero]
  ring

theorem pair_scaled_limit (κ l : ℝ) (hκ : 0 < κ) (hl : 0 < l) (A B D : ℂ) :
    Tendsto (fun x : ℝ => (Real.exp (-l * x) : ℂ) *
      ((A * ((l : ℂ) - κ * Real.tanh (κ * x)) * Complex.exp ((l : ℂ) * x) -
        B * ((l : ℂ) + κ * Real.tanh (κ * x)) * Complex.exp (-(l : ℂ) * x)) / D))
      atTop (𝓝 (A * ((l : ℂ) - κ) / D)) := by
  have ht := (tanh_scaled_limit κ hκ).ofReal.const_mul (κ : ℂ)
  have he := (exp_decay_limit (2 * l) (by positivity)).ofReal
  have hn := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => A) atTop (𝓝 A)).mul
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (l : ℂ)) atTop (𝓝 l)).sub ht)).sub
    (((tendsto_const_nhds : Tendsto (fun _ : ℝ => B) atTop (𝓝 B)).mul
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (l : ℂ)) atTop (𝓝 l)).add ht)).mul he)
  have hd := hn.div_const D
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, sub_zero] at hd
  apply hd.congr
  intro x
  have hw : (Real.exp (-l * x) : ℂ) = Complex.exp (-(l : ℂ) * x) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  have hz : (Real.exp (-(2 * l) * x) : ℂ) =
      Complex.exp (-(l : ℂ) * x) * Complex.exp (-(l : ℂ) * x) := by
    rw [← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hp : Complex.exp (-(l : ℂ) * x) * Complex.exp ((l : ℂ) * x) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [hw, hz]
  simp only [neg_mul] at hp ⊢
  rw [← mul_div_assoc]
  congr 1
  linear_combination -A * ((l : ℂ) - κ * Real.tanh (κ * x)) * hp

open ReflectionlessPotential MeasureTheory

private lemma reconstruct_pair (κ l : ℝ) (f g h : ℝ → ℂ) (A B : ℂ)
    (hinv : ∀ x, h x - (aa κ x : ℂ) * g x = ((l : ℂ) ^ 2 - κ ^ 2) * f x)
    (hpair : ∀ x, g x = A * Complex.exp ((l : ℂ) * x) + B * Complex.exp (-(l : ℂ) * x) ∧
      h x = (l : ℂ) * A * Complex.exp ((l : ℂ) * x) -
        (l : ℂ) * B * Complex.exp (-(l : ℂ) * x))
    (hD : (l : ℂ) ^ 2 - κ ^ 2 ≠ 0) (x : ℝ) :
    f x = (A * ((l : ℂ) - κ * Real.tanh (κ * x)) * Complex.exp ((l : ℂ) * x) -
      B * ((l : ℂ) + κ * Real.tanh (κ * x)) * Complex.exp (-(l : ℂ) * x)) /
      ((l : ℂ) ^ 2 - κ ^ 2) := by
  have hi := hinv x
  rw [(hpair x).1, (hpair x).2] at hi
  dsimp [aa] at hi
  simp only [Complex.ofReal_mul] at hi
  apply (eq_div_iff hD).mpr
  linear_combination -hi

private lemma energy_parameter_eq (κ l : ℝ) (hκ : 0 < κ) (hl : 0 < l)
    (f g h : ℝ → ℂ) (hf : MemLp f 2 volume) (hne : f ≠ 0)
    (hinv : ∀ x, h x - (aa κ x : ℂ) * g x = ((l : ℂ) ^ 2 - κ ^ 2) * f x)
    (hg : ∀ x, HasDerivAt g (h x) x)
    (hh : ∀ x, HasDerivAt h ((l : ℂ) ^ 2 * g x) x) : l = κ := by
  by_contra hneparam
  have hdreal : l ^ 2 - κ ^ 2 ≠ 0 := by
    intro he
    have heq : l = κ := by nlinarith
    exact hneparam heq
  have hD : (l : ℂ) ^ 2 - κ ^ 2 ≠ 0 := by exact_mod_cast hdreal
  have hdiff : (l : ℂ) - κ ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hneparam
  obtain ⟨A, B, hp⟩ := free_negative_ode_classification l hl g h hg hh
  have hfx := reconstruct_pair κ l f g h A B hinv hp hD
  have hlim := pair_scaled_limit κ l hκ hl A B ((l : ℂ) ^ 2 - κ ^ 2)
  have hlimf : Tendsto (fun x : ℝ => (Real.exp (-l * x) : ℂ) * f x) atTop
      (𝓝 (A * ((l : ℂ) - κ) / ((l : ℂ) ^ 2 - κ ^ 2))) := by
    simpa only [← hfx] using hlim
  have hA : A = 0 := by
    have hz := l2_scaled_limit_eq_zero f hf l hl.le _ hlimf
    exact (mul_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right hD)).resolve_right hdiff
  have hfneg : MemLp (fun x : ℝ => f (-x)) 2 volume :=
    hf.comp_measurePreserving (Measure.measurePreserving_neg volume)
  have hnfx (x : ℝ) : f (-x) =
      ((-B) * ((l : ℂ) - κ * Real.tanh (κ * x)) * Complex.exp ((l : ℂ) * x) -
        (-A) * ((l : ℂ) + κ * Real.tanh (κ * x)) * Complex.exp (-(l : ℂ) * x)) /
        ((l : ℂ) ^ 2 - κ ^ 2) := by
    rw [hfx (-x)]
    simp only [mul_neg, Real.tanh_neg, Complex.ofReal_neg, neg_mul, mul_neg, neg_neg]
    ring
  have hnlim := pair_scaled_limit κ l hκ hl (-B) (-A) ((l : ℂ) ^ 2 - κ ^ 2)
  have hnlimf : Tendsto (fun x : ℝ => (Real.exp (-l * x) : ℂ) * f (-x)) atTop
      (𝓝 ((-B) * ((l : ℂ) - κ) / ((l : ℂ) ^ 2 - κ ^ 2))) := by
    simpa only [← hnfx] using hnlim
  have hB : B = 0 := by
    have hz := l2_scaled_limit_eq_zero (fun x => f (-x)) hfneg l hl.le _ hnlimf
    have hb := (mul_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right hD)).resolve_right hdiff
    simpa using hb
  apply hne
  funext x
  simp [hfx x, hA, hB]

private lemma resonant_reconstruction (κ : ℝ) (hκ : 0 < κ) (f f' g h : ℝ → ℂ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hg : ∀ x, HasDerivAt g (h x) x)
    (hgf : ∀ x, g x = f' x + (aa κ x : ℂ) * f x)
    (hinv : ∀ x, h x - (aa κ x : ℂ) * g x = 0) :
    ∀ x, f x = (f 0 + g 0 * primitiveCoshSq κ x) / (Real.cosh (κ * x) : ℂ) := by
  have hc (x : ℝ) := ((Real.hasDerivAt_cosh (κ * x)).comp x
    ((hasDerivAt_id x).const_mul κ)).ofReal_comp
  have hcn (x : ℝ) : (Real.cosh (κ * x) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.cosh_pos (κ * x))
  have hquot (x : ℝ) : HasDerivAt (fun t => g t / (Real.cosh (κ * t) : ℂ)) 0 x := by
    have hd := (hg x).div (hc x) (hcn x)
    convert! hd using 1
    simp only [Function.comp_apply, mul_one, Complex.ofReal_mul]
    have hi : h x = (aa κ x : ℂ) * g x := sub_eq_zero.mp (hinv x)
    rw [hi]
    dsimp [aa]
    rw [Real.tanh_eq_sinh_div_cosh]
    simp only [Complex.ofReal_mul, Complex.ofReal_div]
    have halg (a b c z : ℂ) (hn : c ≠ 0) :
        ((a * (b / c)) * z * c - z * (b * a)) / c ^ 2 = 0 := by
      field_simp [hn]
      ring
    exact (halg κ (Real.sinh (κ * x)) (Real.cosh (κ * x)) (g x) (hcn x)).symm
  have hgform (x : ℝ) : g x = g 0 * (Real.cosh (κ * x) : ℂ) := by
    have he := is_const_of_deriv_eq_zero (fun t => (hquot t).differentiableAt)
      (fun t => (hquot t).deriv) x 0
    simp only [mul_zero, Real.cosh_zero, Complex.ofReal_one, div_one] at he
    exact (div_eq_iff (hcn x)).mp he
  let F : ℝ → ℂ := fun x => f x * (Real.cosh (κ * x) : ℂ) -
    g 0 * (primitiveCoshSq κ x : ℂ)
  have hF (x : ℝ) : HasDerivAt F 0 x := by
    have hd := ((hf x).mul (hc x)).sub
      (((primitiveCoshSq_deriv κ x hκ.ne').ofReal_comp).const_mul (g 0))
    convert! hd using 1
    simp only [Function.comp_apply, mul_one, Complex.ofReal_mul, Complex.ofReal_pow]
    have he := hgf x
    rw [hgform x] at he
    dsimp [aa] at he
    rw [Real.tanh_eq_sinh_div_cosh] at he
    simp only [Complex.ofReal_mul, Complex.ofReal_div] at he
    have he' := (eq_div_iff (hcn x)).mp
      (show (g 0 * (Real.cosh (κ * x) : ℂ) - f' x) =
        ((κ : ℂ) * (Real.sinh (κ * x) : ℂ) * f x) / (Real.cosh (κ * x) : ℂ) by
          linear_combination he)
    linear_combination he'
  intro x
  have he := is_const_of_deriv_eq_zero (fun t => (hF t).differentiableAt)
    (fun t => (hF t).deriv) x 0
  simp only [F, primitiveCoshSq, mul_zero, Real.cosh_zero, Complex.ofReal_one,
    Real.sinh_zero, zero_div, add_zero, Complex.ofReal_zero, mul_one, sub_zero] at he
  apply (eq_div_iff (hcn x)).mpr
  dsimp [primitiveCoshSq]
  linear_combination he

theorem solution (κ E : ℝ) (hκ : 0 < κ) (hE : E < 0) (f : ℝ → ℂ)
    (hf : IsEigenstate κ E f) (hL2 : MemLp f 2 volume) (hne : f ≠ 0) :
    E = -(κ ^ 2 / 2) ∧ ∃ c : ℂ, ∀ x, f x = c * psi0 κ x := by
  let l : ℝ := Real.sqrt (-2 * E)
  have hl : 0 < l := Real.sqrt_pos.mpr (by linarith)
  have hl2 : l ^ 2 = -2 * E := Real.sq_sqrt (by linarith)
  obtain ⟨f', f'', hf, hf', he⟩ := hf
  have hd (x : ℝ) : HasDerivAt f' (((l : ℂ) ^ 2 - 2 * qq κ x) * f x) x := by
    have he' := he x
    have hl2c : (l : ℂ) ^ 2 = -2 * (E : ℂ) := by exact_mod_cast hl2
    convert! hf' x using 1
    dsimp [V, qq] at he' ⊢
    simp only [Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_div] at he' ⊢
    rw [hl2c]
    linear_combination 2 * he'
  obtain ⟨g, h, hg, hh, hgf, hinv⟩ := darboux_free_equation κ l f f' hf hd
  have hlκ := energy_parameter_eq κ l hκ hl f g h hL2 hne hinv hg hh
  have hEeq : E = -(κ ^ 2 / 2) := by rw [hlκ] at hl2; linarith
  refine ⟨hEeq, ?_⟩
  have hinv0 (x : ℝ) : h x - (aa κ x : ℂ) * g x = 0 := by
    simpa [hlκ] using hinv x
  have hform := resonant_reconstruction κ hκ f f' g h hf hg hgf hinv0
  have hlim := resonant_scaled_limit κ hκ (f 0) (g 0)
  have hlimf : Tendsto (fun x : ℝ => (Real.exp (-κ * x) : ℂ) * f x) atTop
      (𝓝 (g 0 / (4 * κ))) := by simpa only [← hform] using hlim
  have hg0 : g 0 = 0 := by
    have hz := l2_scaled_limit_eq_zero f hL2 κ hκ.le _ hlimf
    exact (div_eq_zero_iff.mp hz).resolve_right
      (by exact_mod_cast (by positivity : (4 : ℝ) * κ ≠ 0))
  have hs : (Real.sqrt (κ / 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < κ / 2)).ne'
  refine ⟨f 0 / Real.sqrt (κ / 2), fun x => ?_⟩
  rw [hform x, hg0]
  simp only [zero_mul, add_zero, psi0, Complex.ofReal_div]
  field_simp

-- Prove2me | solution 1 for SpikedWishart.SoftEdge.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T06:01:20.72171+00:00
-- url     : https://prove2.me/submissions/6823d959-8963-424a-9ef3-0355bb15aafc

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open Complex

set_option autoImplicit false

namespace SWLem31
open SpikedWishart.SoftEdge

theorem log_re' (w : ℂ) : (Complex.log w).re = Real.log (w.re * w.re + w.im * w.im) / 2 := by
  rw [Complex.log_re, Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg w), Complex.normSq_apply]

theorem reF (γ q : ℝ) (z : ℂ) : (fFn γ q z).re = -(mu γ * (z.re - q))
    + Real.log (z.re * z.re + z.im * z.im) / 2
    - 1 / γ ^ 2 * (Real.log ((1 - z.re) * (1 - z.re) + z.im * z.im) / 2) := by
  have h1 : (1 / (γ : ℂ) ^ 2) = ((1 / γ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have h2 := log_re' z
  have h3 : (Complex.log (1 - z)).re = Real.log ((1 - z.re) * (1 - z.re) + z.im * z.im) / 2 := by
    rw [log_re']; congr 2; simp
  show (( -(mu γ : ℂ) * (z - q) + Complex.log z - (1 / (γ : ℂ) ^ 2) * Complex.log (1 - z))).re = _
  rw [h1, Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul, h2, h3, neg_mul,
    Complex.neg_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.ofReal_re]

theorem omega_re : (Complex.exp ((Real.pi / 3 : ℝ) * I)).re = 1 / 2 := by
  rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]

theorem omega_im : (Complex.exp ((Real.pi / 3 : ℝ) * I)).im = Real.sqrt 3 / 2 := by
  rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]

theorem omega_eq : Complex.exp ((Real.pi / 3 : ℝ) * I)
    = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by
  apply Complex.ext
  · rw [omega_re]; simp
  · rw [omega_im]; simp

theorem pc_facts (γ : ℝ) (hγ : 1 ≤ γ) :
    1 / 2 ≤ pc γ ∧ pc γ < 1 ∧ mu γ = 1 / pc γ ^ 2 ∧ 1 / γ ^ 2 = (1 - pc γ) ^ 2 / pc γ ^ 2 := by
  have hγ0 : 0 < γ := by linarith
  have h1 : 0 < γ + 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold pc; rw [le_div_iff₀ h1]; linarith
  · unfold pc; rw [div_lt_one h1]; linarith
  · unfold mu pc; field_simp; ring
  · unfold pc; field_simp; ring

theorem mu_ge_one (γ : ℝ) (hγ : 1 ≤ γ) : 1 ≤ mu γ := by
  have hγ0 : 0 < γ := by linarith
  unfold mu
  have : 1 ≤ (1 + γ) / γ := by rw [le_div_iff₀ hγ0]; linarith
  nlinarith

/-- Part 1 in coordinates: `z = p + t e^{iπ/3}`. -/
theorem part1 (γ q : ℝ) (hγ : 1 ≤ γ) :
    StrictAntiOn (fun t : ℝ => -(mu γ * (pc γ + t / 2 - q))
      + Real.log (t ^ 2 + pc γ * t + pc γ ^ 2) / 2
      - 1 / γ ^ 2 * (Real.log (t ^ 2 - (1 - pc γ) * t + (1 - pc γ) ^ 2) / 2))
      (Set.Icc 0 (2 * (1 - pc γ))) := by
  obtain ⟨hp1, hp2, hμ, hg⟩ := pc_facts γ hγ
  set p := pc γ with hpdef
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < 1 - p := by linarith
  have hA0 : ∀ t : ℝ, 0 < t ^ 2 + p * t + p ^ 2 := fun t => by nlinarith [sq_nonneg (t + p / 2)]
  have hB0 : ∀ t : ℝ, 0 < t ^ 2 - (1 - p) * t + (1 - p) ^ 2 := fun t => by
    nlinarith [sq_nonneg (t - (1 - p) / 2)]
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => -(mu γ * (p + t / 2 - q))
      + Real.log (t ^ 2 + p * t + p ^ 2) / 2
      - 1 / γ ^ 2 * (Real.log (t ^ 2 - (1 - p) * t + (1 - p) ^ 2) / 2))
      (-(mu γ * (1 / 2)) + (2 * t + p) / (t ^ 2 + p * t + p ^ 2) / 2
        - 1 / γ ^ 2 * ((2 * t - (1 - p)) / (t ^ 2 - (1 - p) * t + (1 - p) ^ 2) / 2)) t := by
    intro t
    have hA : HasDerivAt (fun t : ℝ => t ^ 2 + p * t + p ^ 2) (2 * t + p) t := by
      have := ((hasDerivAt_pow 2 t).add ((hasDerivAt_id' t).const_mul p)).add_const (p ^ 2)
      exact this.congr_deriv (by norm_num)
    have hB : HasDerivAt (fun t : ℝ => t ^ 2 - (1 - p) * t + (1 - p) ^ 2) (2 * t - (1 - p)) t := by
      have := ((hasDerivAt_pow 2 t).sub ((hasDerivAt_id' t).const_mul (1 - p))).add_const ((1 - p) ^ 2)
      exact this.congr_deriv (by norm_num)
    have hL : HasDerivAt (fun t : ℝ => -(mu γ * (p + t / 2 - q))) (-(mu γ * (1 / 2))) t :=
      ((((hasDerivAt_id' t).div_const 2).const_add p).sub_const q).const_mul (mu γ) |>.neg
    exact (hL.add ((hA.log (hA0 t).ne').div_const 2)).sub
      (((hB.log (hB0 t).ne').div_const 2).const_mul (1 / γ ^ 2))
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 (2 * (1 - p)))
  · intro t _; exact (hd t).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0 < t := ht.1
    have ht1 : t < 2 * (1 - p) := ht.2
    rw [(hd t).deriv, hμ, hg]
    have hA := hA0 t
    have hB := hB0 t
    have hX0 : 0 ≤ (1 - 2 * p) * (t - 2 * (1 - p)) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    have hX : 0 < 2 * p * (1 - p) + (1 - 2 * p) * t + t ^ 2 := by nlinarith
    have hP : 0 < 2 * p ^ 2 * (t ^ 2 + p * t + p ^ 2) * (t ^ 2 - (1 - p) * t + (1 - p) ^ 2) := by
      positivity
    have key : (-(1 / p ^ 2 * (1 / 2)) + (2 * t + p) / (t ^ 2 + p * t + p ^ 2) / 2
        - (1 - p) ^ 2 / p ^ 2 * ((2 * t - (1 - p)) / (t ^ 2 - (1 - p) * t + (1 - p) ^ 2) / 2))
        * (2 * p ^ 2 * (t ^ 2 + p * t + p ^ 2) * (t ^ 2 - (1 - p) * t + (1 - p) ^ 2))
        = -(t ^ 2 * (2 * p * (1 - p) + (1 - 2 * p) * t + t ^ 2)) := by
      have key1 : ∀ A B : ℝ, A ≠ 0 → B ≠ 0 →
          (-(1 / p ^ 2 * (1 / 2)) + (2 * t + p) / A / 2
            - (1 - p) ^ 2 / p ^ 2 * ((2 * t - (1 - p)) / B / 2)) * (2 * p ^ 2 * A * B)
          = -(A * B) + p ^ 2 * (2 * t + p) * B - (1 - p) ^ 2 * (2 * t - (1 - p)) * A := by
        intro A B hA hB
        field_simp
      rw [key1 _ _ hA.ne' hB.ne']
      ring
    by_contra hcon
    rw [not_lt] at hcon
    have := mul_nonneg hcon hP.le
    rw [key] at this
    have : 0 < t ^ 2 * (2 * p * (1 - p) + (1 - 2 * p) * t + t ^ 2) := by positivity
    linarith

/-- Part 2 in coordinates: `z = 1 + x + i √3 (1 - p)`. -/
theorem part2 (γ q : ℝ) (hγ : 1 ≤ γ) :
    StrictAntiOn (fun x : ℝ => -(mu γ * (1 + x - q))
      + Real.log ((1 + x) ^ 2 + 3 * (1 - pc γ) ^ 2) / 2
      - 1 / γ ^ 2 * (Real.log (x ^ 2 + 3 * (1 - pc γ) ^ 2) / 2)) (Set.Ici 0) := by
  obtain ⟨hp1, hp2, _, _⟩ := pc_facts γ hγ
  set r := 1 - pc γ with hrdef
  have hr0 : 0 < r := by linarith
  have hA0 : ∀ x : ℝ, 0 < (1 + x) ^ 2 + 3 * r ^ 2 := fun x => by positivity
  have hB0 : ∀ x : ℝ, 0 < x ^ 2 + 3 * r ^ 2 := fun x => by positivity
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => -(mu γ * (1 + x - q))
      + Real.log ((1 + x) ^ 2 + 3 * r ^ 2) / 2
      - 1 / γ ^ 2 * (Real.log (x ^ 2 + 3 * r ^ 2) / 2))
      (-(mu γ * 1) + (2 * (1 + x)) / ((1 + x) ^ 2 + 3 * r ^ 2) / 2
        - 1 / γ ^ 2 * ((2 * x) / (x ^ 2 + 3 * r ^ 2) / 2)) x := by
    intro x
    have hA : HasDerivAt (fun x : ℝ => (1 + x) ^ 2 + 3 * r ^ 2) (2 * (1 + x)) x := by
      have := (((hasDerivAt_id' x).const_add 1).pow 2).add_const (3 * r ^ 2)
      exact this.congr_deriv (by norm_num)
    have hB : HasDerivAt (fun x : ℝ => x ^ 2 + 3 * r ^ 2) (2 * x) x := by
      have := (hasDerivAt_pow 2 x).add_const (3 * r ^ 2)
      exact this.congr_deriv (by norm_num)
    have hL : HasDerivAt (fun x : ℝ => -(mu γ * (1 + x - q))) (-(mu γ * 1)) x :=
      (((hasDerivAt_id' x).const_add 1).sub_const q).const_mul (mu γ) |>.neg
    exact (hL.add ((hA.log (hA0 x).ne').div_const 2)).sub
      (((hB.log (hB0 x).ne').div_const 2).const_mul (1 / γ ^ 2))
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · intro x _; exact (hd x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := hx
    rw [(hd x).deriv]
    have h1 : 0 ≤ 2 * x / (x ^ 2 + 3 * r ^ 2) / 2 := by positivity
    have h2 : 2 * (1 + x) / ((1 + x) ^ 2 + 3 * r ^ 2) / 2 < 1 := by
      rw [div_div, div_lt_one (by positivity)]; nlinarith
    have hc0 : 0 ≤ 1 / γ ^ 2 * (2 * x / (x ^ 2 + 3 * r ^ 2) / 2) := by positivity
    have hmu := mu_ge_one γ hγ
    linarith

theorem main1 (γ q ε : ℝ) (M : ℕ) (hγ : 1 ≤ γ) (hε : 0 < ε) (hM : 0 < M) :
    StrictAntiOn (fun t : ℝ => (fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp ((Real.pi / 3 : ℝ) * I))).re)
      (Set.Icc (ε / (2 * nu γ * (M : ℝ) ^ (1 / 3 : ℝ))) (2 * (1 - pc γ))) := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have heq : (fun t : ℝ => (fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp ((Real.pi / 3 : ℝ) * I))).re)
      = (fun t : ℝ => -(mu γ * (pc γ + t / 2 - q))
      + Real.log (t ^ 2 + pc γ * t + pc γ ^ 2) / 2
      - 1 / γ ^ 2 * (Real.log (t ^ 2 - (1 - pc γ) * t + (1 - pc γ) ^ 2) / 2)) := by
    funext t
    rw [reF]
    have hre : ((pc γ : ℂ) + (t : ℂ) * exp ((Real.pi / 3 : ℝ) * I)).re = pc γ + t / 2 := by
      rw [omega_eq]; simp; ring
    have him : ((pc γ : ℂ) + (t : ℂ) * exp ((Real.pi / 3 : ℝ) * I)).im
        = t * (Real.sqrt 3 / 2) := by
      rw [omega_eq]; simp
    rw [hre, him]
    have e1 : (pc γ + t / 2) * (pc γ + t / 2) + t * (Real.sqrt 3 / 2) * (t * (Real.sqrt 3 / 2))
        = t ^ 2 + pc γ * t + pc γ ^ 2 := by linear_combination (t ^ 2 / 4) * hs
    have e2 : (1 - (pc γ + t / 2)) * (1 - (pc γ + t / 2))
        + t * (Real.sqrt 3 / 2) * (t * (Real.sqrt 3 / 2))
        = t ^ 2 - (1 - pc γ) * t + (1 - pc γ) ^ 2 := by linear_combination (t ^ 2 / 4) * hs
    rw [e1, e2]
  rw [heq]
  have h0 : 0 ≤ ε / (2 * nu γ * (M : ℝ) ^ (1 / 3 : ℝ)) := by
    have hγ0 : (0:ℝ) < γ := by linarith
    have : 0 < nu γ := by unfold nu; positivity
    positivity
  exact (part1 γ q hγ).mono (fun t ht => ⟨le_trans h0 ht.1, ht.2⟩)

theorem main2 (γ q R : ℝ) (hγ : 1 ≤ γ) :
    StrictAntiOn
      (fun x : ℝ => (fFn γ q ((pc γ : ℂ) + 2 * (1 - pc γ) * exp ((Real.pi / 3 : ℝ) * I) + x)).re)
      (Set.Icc 0 R) := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have heq : (fun x : ℝ =>
      (fFn γ q ((pc γ : ℂ) + 2 * (1 - pc γ) * exp ((Real.pi / 3 : ℝ) * I) + x)).re)
      = (fun x : ℝ => -(mu γ * (1 + x - q))
      + Real.log ((1 + x) ^ 2 + 3 * (1 - pc γ) ^ 2) / 2
      - 1 / γ ^ 2 * (Real.log (x ^ 2 + 3 * (1 - pc γ) ^ 2) / 2)) := by
    funext x
    rw [reF]
    have hre : ((pc γ : ℂ) + 2 * (1 - pc γ) * exp ((Real.pi / 3 : ℝ) * I) + x).re = 1 + x := by
      rw [omega_eq]; simp; ring
    have him : ((pc γ : ℂ) + 2 * (1 - pc γ) * exp ((Real.pi / 3 : ℝ) * I) + x).im
        = Real.sqrt 3 * (1 - pc γ) := by
      rw [omega_eq]; simp; ring
    rw [hre, him]
    have e1 : (1 + x) * (1 + x) + Real.sqrt 3 * (1 - pc γ) * (Real.sqrt 3 * (1 - pc γ))
        = (1 + x) ^ 2 + 3 * (1 - pc γ) ^ 2 := by
      linear_combination ((1 - pc γ) ^ 2) * hs
    have e2 : (1 - (1 + x)) * (1 - (1 + x)) + Real.sqrt 3 * (1 - pc γ) * (Real.sqrt 3 * (1 - pc γ))
        = x ^ 2 + 3 * (1 - pc γ) ^ 2 := by
      linear_combination ((1 - pc γ) ^ 2) * hs
    rw [e1, e2]
  rw [heq]
  exact (part2 γ q hγ).mono (fun x hx => Set.mem_Ici.mpr hx.1)

theorem main3 (γ q R y : ℝ) (hγ : 1 ≤ γ) (hR : 1 ≤ R) (hy0 : 0 ≤ y)
    (hy : y ≤ Real.sqrt 3 * (1 - pc γ)) :
    (fFn γ q (1 + R + (y : ℂ) * I)).re ≤
      (fFn γ q ((pc γ : ℂ) + 2 * (1 - pc γ) * exp ((Real.pi / 3 : ℝ) * I))).re := by
  obtain ⟨hp1, hp2, _, _⟩ := pc_facts γ hγ
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [reF, reF]
  have hre1 : (1 + (R : ℂ) + (y : ℂ) * I).re = 1 + R := by simp
  have him1 : (1 + (R : ℂ) + (y : ℂ) * I).im = y := by simp
  have hre2 : ((pc γ : ℂ) + 2 * (1 - pc γ) * exp ((Real.pi / 3 : ℝ) * I)).re = 1 := by
    rw [omega_eq]; simp; ring
  have him2 : ((pc γ : ℂ) + 2 * (1 - pc γ) * exp ((Real.pi / 3 : ℝ) * I)).im
      = Real.sqrt 3 * (1 - pc γ) := by
    rw [omega_eq]; simp; ring
  rw [hre1, him1, hre2, him2]
  set r := 1 - pc γ with hrdef
  have hr0 : 0 < r := by linarith
  have hr1 : r ≤ 1 / 2 := by linarith
  have hd3 : Real.sqrt 3 * r * (Real.sqrt 3 * r) = 3 * r ^ 2 := by linear_combination (r ^ 2) * hs
  have hyy : y * y ≤ 3 * r ^ 2 := by
    have : y * y ≤ Real.sqrt 3 * r * (Real.sqrt 3 * r) := mul_self_le_mul_self hy0 hy
    linarith
  have hmu := mu_ge_one γ hγ
  have hc0 : 0 ≤ 1 / γ ^ 2 := by positivity
  -- log((1+R)^2 + y^2) ≤ 2R
  have hY0 : 0 < (1 + R) * (1 + R) + y * y := by nlinarith
  have hY : (1 + R) * (1 + R) + y * y ≤ Real.exp (2 * R) := by
    have := Real.quadratic_le_exp_of_nonneg (by linarith : (0:ℝ) ≤ 2 * R)
    nlinarith
  have hL1 : Real.log ((1 + R) * (1 + R) + y * y) ≤ 2 * R := by
    have := Real.log_le_log hY0 hY
    rwa [Real.log_exp] at this
  -- log of the p* modulus is ≥ 0
  have hL2 : 0 ≤ Real.log (1 * 1 + Real.sqrt 3 * r * (Real.sqrt 3 * r)) := by
    apply Real.log_nonneg; rw [hd3]; nlinarith
  -- the 1 - z terms: log(R^2 + y^2) ≥ log(3 r^2)
  have hW0 : 0 < (1 - 1) * (1 - 1) + Real.sqrt 3 * r * (Real.sqrt 3 * r) := by
    rw [hd3]; positivity
  have hW : (1 - 1) * (1 - 1) + Real.sqrt 3 * r * (Real.sqrt 3 * r)
      ≤ (1 - (1 + R)) * (1 - (1 + R)) + y * y := by
    rw [hd3]; nlinarith
  have hL3 : Real.log ((1 - 1) * (1 - 1) + Real.sqrt 3 * r * (Real.sqrt 3 * r))
      ≤ Real.log ((1 - (1 + R)) * (1 - (1 + R)) + y * y) := Real.log_le_log hW0 hW
  have hL4 : 1 / γ ^ 2 * (Real.log ((1 - 1) * (1 - 1) + Real.sqrt 3 * r * (Real.sqrt 3 * r)) / 2)
      ≤ 1 / γ ^ 2 * (Real.log ((1 - (1 + R)) * (1 - (1 + R)) + y * y) / 2) :=
    mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right (by norm_num)).mpr hL3) hc0
  have hmR : 1 * R ≤ mu γ * R := mul_le_mul_of_nonneg_right hmu (by linarith)
  have x1 : mu γ * (1 + R - q) = mu γ * (1 - q) + mu γ * R := by ring
  rw [x1]
  generalize Real.log ((1 + R) * (1 + R) + y * y) = A at hL1 ⊢
  generalize Real.log (1 * 1 + Real.sqrt 3 * r * (Real.sqrt 3 * r)) = B at hL2 ⊢
  generalize 1 / γ ^ 2 * (Real.log ((1 - 1) * (1 - 1) + Real.sqrt 3 * r * (Real.sqrt 3 * r)) / 2) = C at hL4 ⊢
  generalize 1 / γ ^ 2 * (Real.log ((1 - (1 + R)) * (1 - (1 + R)) + y * y) / 2) = D at hL4 ⊢
  generalize mu γ * R = E at hmR ⊢
  linarith

end SWLem31

open Complex SpikedWishart.SoftEdge in
theorem solution :
    (∀ (γ q ε : ℝ) (M : ℕ), 1 ≤ γ → 0 < ε → 0 < M →
      StrictAntiOn (fun t : ℝ => (fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp ((Real.pi / 3 : ℝ) * I))).re)
        (Set.Icc (ε / (2 * nu γ * (M : ℝ) ^ (1 / 3 : ℝ))) (2 * (1 - pc γ)))) ∧
    (∀ (γ q R : ℝ), 1 ≤ γ →
      StrictAntiOn
        (fun x : ℝ => (fFn γ q ((pc γ : ℂ) + 2 * (1 - pc γ) * exp ((Real.pi / 3 : ℝ) * I) + x)).re)
        (Set.Icc 0 R)) ∧
    (∀ γ₀ : ℝ, 1 ≤ γ₀ → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ (γ q R y : ℝ), 1 ≤ γ → γ ≤ γ₀ → R₀ ≤ R →
      0 ≤ y → y ≤ Real.sqrt 3 * (1 - pc γ) →
      (fFn γ q (1 + R + (y : ℂ) * I)).re ≤
        (fFn γ q ((pc γ : ℂ) + 2 * (1 - pc γ) * exp ((Real.pi / 3 : ℝ) * I))).re) := by
  refine ⟨fun γ q ε M hγ hε hM => SWLem31.main1 γ q ε M hγ hε hM,
    fun γ q R hγ => SWLem31.main2 γ q R hγ, fun γ₀ _ => ⟨1, by norm_num, ?_⟩⟩
  intro γ q R y hγ _ hR hy0 hy
  exact SWLem31.main3 γ q R y hγ hR hy0 hy

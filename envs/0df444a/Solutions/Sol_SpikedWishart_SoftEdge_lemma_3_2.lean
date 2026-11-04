-- Prove2me | solution 1 for SpikedWishart.SoftEdge.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T00:40:45.453062+00:00
-- url     : https://prove2.me/submissions/ed225664-8e06-44de-aefb-5713f01530b2

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open Complex

set_option autoImplicit false

namespace SWLem32
open SpikedWishart.SoftEdge

theorem log_re' (w : ℂ) : (Complex.log w).re = Real.log (w.re * w.re + w.im * w.im) / 2 := by
  rw [Complex.log_re, Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg w), Complex.normSq_apply]

theorem reF (γ q : ℝ) (z : ℂ) : (-fFn γ q z).re = mu γ * (z.re - q)
    - Real.log (z.re * z.re + z.im * z.im) / 2
    + 1 / γ ^ 2 * (Real.log ((1 - z.re) * (1 - z.re) + z.im * z.im) / 2) := by
  have h1 : (1 / (γ : ℂ) ^ 2) = ((1 / γ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have h2 := log_re' z
  have h3 : (Complex.log (1 - z)).re = Real.log ((1 - z.re) * (1 - z.re) + z.im * z.im) / 2 := by
    rw [log_re']; congr 2; simp
  show (-( -(mu γ : ℂ) * (z - q) + Complex.log z - (1 / (γ : ℂ) ^ 2) * Complex.log (1 - z))).re = _
  rw [h1, Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul, h2, h3, neg_mul,
    Complex.neg_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.ofReal_re]
  ring

theorem omega_re : (Complex.exp ((2 * Real.pi / 3 : ℝ) * I)).re = -1 / 2 := by
  rw [Complex.exp_ofReal_mul_I_re, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

theorem omega_im : (Complex.exp ((2 * Real.pi / 3 : ℝ) * I)).im = Real.sqrt 3 / 2 := by
  rw [Complex.exp_ofReal_mul_I_im, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
    Real.sin_pi_sub, Real.sin_pi_div_three]

theorem omega_eq : Complex.exp ((2 * Real.pi / 3 : ℝ) * I)
    = ((-1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by
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

theorem inv_sq_le_one (γ : ℝ) (hγ : 1 ≤ γ) : 1 / γ ^ 2 ≤ 1 := by
  rw [div_le_one (by positivity)]; nlinarith

/-- Part 1 in coordinates. -/
theorem part1 (γ q : ℝ) (hγ : 1 ≤ γ) :
    StrictAntiOn (fun t : ℝ => mu γ * (pc γ - t / 2 - q)
      - Real.log (t ^ 2 - pc γ * t + pc γ ^ 2) / 2
      + 1 / γ ^ 2 * (Real.log (t ^ 2 + (1 - pc γ) * t + (1 - pc γ) ^ 2) / 2)) (Set.Ici 0) := by
  obtain ⟨hp1, hp2, hμ, hg⟩ := pc_facts γ hγ
  set p := pc γ with hpdef
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < 1 - p := by linarith
  have hA0 : ∀ t : ℝ, 0 < t ^ 2 - p * t + p ^ 2 := fun t => by nlinarith [sq_nonneg (t - p / 2)]
  have hB0 : ∀ t : ℝ, 0 < t ^ 2 + (1 - p) * t + (1 - p) ^ 2 := fun t => by
    nlinarith [sq_nonneg (t + (1 - p) / 2)]
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => mu γ * (p - t / 2 - q)
      - Real.log (t ^ 2 - p * t + p ^ 2) / 2
      + 1 / γ ^ 2 * (Real.log (t ^ 2 + (1 - p) * t + (1 - p) ^ 2) / 2))
      (mu γ * (-(1 / 2)) - (2 * t - p) / (t ^ 2 - p * t + p ^ 2) / 2
        + 1 / γ ^ 2 * ((2 * t + (1 - p)) / (t ^ 2 + (1 - p) * t + (1 - p) ^ 2) / 2)) t := by
    intro t
    have hA : HasDerivAt (fun t : ℝ => t ^ 2 - p * t + p ^ 2) (2 * t - p) t := by
      have := ((hasDerivAt_pow 2 t).sub ((hasDerivAt_id' t).const_mul p)).add_const (p ^ 2)
      exact this.congr_deriv (by norm_num)
    have hB : HasDerivAt (fun t : ℝ => t ^ 2 + (1 - p) * t + (1 - p) ^ 2) (2 * t + (1 - p)) t := by
      have := ((hasDerivAt_pow 2 t).add ((hasDerivAt_id' t).const_mul (1 - p))).add_const ((1 - p) ^ 2)
      exact this.congr_deriv (by norm_num)
    have hL : HasDerivAt (fun t : ℝ => mu γ * (p - t / 2 - q)) (mu γ * (-(1 / 2))) t :=
      ((((hasDerivAt_id' t).div_const 2).const_sub p).sub_const q).const_mul (mu γ)
    exact (hL.sub ((hA.log (hA0 t).ne').div_const 2)).add
      (((hB.log (hB0 t).ne').div_const 2).const_mul (1 / γ ^ 2))
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · intro t _; exact (hd t).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have ht0 : 0 < t := ht
    rw [(hd t).deriv, hμ, hg]
    have hA := hA0 t
    have hB := hB0 t
    have hX : 0 < 2 * p * (1 - p) + (2 * p - 1) * t + t ^ 2 := by nlinarith
    have hP : 0 < 2 * p ^ 2 * (t ^ 2 - p * t + p ^ 2) * (t ^ 2 + (1 - p) * t + (1 - p) ^ 2) := by
      positivity
    have key : (1 / p ^ 2 * (-(1 / 2)) - (2 * t - p) / (t ^ 2 - p * t + p ^ 2) / 2
        + (1 - p) ^ 2 / p ^ 2 * ((2 * t + (1 - p)) / (t ^ 2 + (1 - p) * t + (1 - p) ^ 2) / 2))
        * (2 * p ^ 2 * (t ^ 2 - p * t + p ^ 2) * (t ^ 2 + (1 - p) * t + (1 - p) ^ 2))
        = -(t ^ 2 * (2 * p * (1 - p) + (2 * p - 1) * t + t ^ 2)) := by
      have key1 : ∀ A B : ℝ, A ≠ 0 → B ≠ 0 →
          (1 / p ^ 2 * (-(1 / 2)) - (2 * t - p) / A / 2
            + (1 - p) ^ 2 / p ^ 2 * ((2 * t + (1 - p)) / B / 2)) * (2 * p ^ 2 * A * B)
          = -(A * B) - p ^ 2 * (2 * t - p) * B + (1 - p) ^ 2 * (2 * t + (1 - p)) * A := by
        intro A B hA hB
        field_simp
      rw [key1 _ _ hA.ne' hB.ne']
      ring
    by_contra hcon
    rw [not_lt] at hcon
    have := mul_nonneg hcon hP.le
    rw [key] at this
    have : 0 < t ^ 2 * (2 * p * (1 - p) + (2 * p - 1) * t + t ^ 2) := by positivity
    linarith

/-- Part 2 in coordinates. -/
theorem part2 (γ q : ℝ) (hγ : 1 ≤ γ) :
    StrictAntiOn (fun x : ℝ => mu γ * (-x - q)
      - Real.log (x ^ 2 + 3 * pc γ ^ 2) / 2
      + 1 / γ ^ 2 * (Real.log ((1 + x) ^ 2 + 3 * pc γ ^ 2) / 2)) (Set.Ici 0) := by
  obtain ⟨hp1, hp2, hμ, hg⟩ := pc_facts γ hγ
  set p := pc γ with hpdef
  have hp0 : 0 < p := by linarith
  have hA0 : ∀ x : ℝ, 0 < x ^ 2 + 3 * p ^ 2 := fun x => by positivity
  have hB0 : ∀ x : ℝ, 0 < (1 + x) ^ 2 + 3 * p ^ 2 := fun x => by positivity
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => mu γ * (-x - q)
      - Real.log (x ^ 2 + 3 * p ^ 2) / 2
      + 1 / γ ^ 2 * (Real.log ((1 + x) ^ 2 + 3 * p ^ 2) / 2))
      (mu γ * (-1) - (2 * x) / (x ^ 2 + 3 * p ^ 2) / 2
        + 1 / γ ^ 2 * ((2 * (1 + x)) / ((1 + x) ^ 2 + 3 * p ^ 2) / 2)) x := by
    intro x
    have hA : HasDerivAt (fun x : ℝ => x ^ 2 + 3 * p ^ 2) (2 * x) x := by
      have := (hasDerivAt_pow 2 x).add_const (3 * p ^ 2)
      exact this.congr_deriv (by norm_num)
    have hB : HasDerivAt (fun x : ℝ => (1 + x) ^ 2 + 3 * p ^ 2) (2 * (1 + x)) x := by
      have := (((hasDerivAt_id' x).const_add 1).pow 2).add_const (3 * p ^ 2)
      exact this.congr_deriv (by norm_num)
    have hL : HasDerivAt (fun x : ℝ => mu γ * (-x - q)) (mu γ * (-1)) x :=
      (((hasDerivAt_id' x).neg).sub_const q).const_mul (mu γ)
    exact (hL.sub ((hA.log (hA0 x).ne').div_const 2)).add
      (((hB.log (hB0 x).ne').div_const 2).const_mul (1 / γ ^ 2))
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · intro x _; exact (hd x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := hx
    rw [(hd x).deriv]
    have h1 : 0 ≤ 2 * x / (x ^ 2 + 3 * p ^ 2) / 2 := by positivity
    have h2 : 2 * (1 + x) / ((1 + x) ^ 2 + 3 * p ^ 2) / 2 ≤ 1 := by
      rw [div_div, div_le_one (by positivity)]; nlinarith
    have hc0 : 0 ≤ 1 / γ ^ 2 := by positivity
    have h3 : 1 / γ ^ 2 * (2 * (1 + x) / ((1 + x) ^ 2 + 3 * p ^ 2) / 2) ≤ 1 / γ ^ 2 :=
      mul_le_of_le_one_right hc0 h2
    have h4 : 1 / γ ^ 2 < mu γ := by
      rw [hμ, hg]
      apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
      nlinarith
    linarith

theorem main1 (γ q ε : ℝ) (M : ℕ) (hγ : 1 ≤ γ) (hε : 0 < ε) (hM : 0 < M) :
    StrictAntiOn
      (fun t : ℝ => (-fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp ((2 * Real.pi / 3 : ℝ) * I))).re)
      (Set.Icc (3 * ε / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ))) (2 * pc γ)) := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have heq : (fun t : ℝ => (-fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp ((2 * Real.pi / 3 : ℝ) * I))).re)
      = (fun t : ℝ => mu γ * (pc γ - t / 2 - q)
      - Real.log (t ^ 2 - pc γ * t + pc γ ^ 2) / 2
      + 1 / γ ^ 2 * (Real.log (t ^ 2 + (1 - pc γ) * t + (1 - pc γ) ^ 2) / 2)) := by
    funext t
    rw [reF]
    have hre : ((pc γ : ℂ) + (t : ℂ) * exp ((2 * Real.pi / 3 : ℝ) * I)).re = pc γ - t / 2 := by
      rw [omega_eq]; simp; ring
    have him : ((pc γ : ℂ) + (t : ℂ) * exp ((2 * Real.pi / 3 : ℝ) * I)).im
        = t * (Real.sqrt 3 / 2) := by
      rw [omega_eq]; simp
    rw [hre, him]
    have e1 : (pc γ - t / 2) * (pc γ - t / 2) + t * (Real.sqrt 3 / 2) * (t * (Real.sqrt 3 / 2))
        = t ^ 2 - pc γ * t + pc γ ^ 2 := by linear_combination (t ^ 2 / 4) * hs
    have e2 : (1 - (pc γ - t / 2)) * (1 - (pc γ - t / 2))
        + t * (Real.sqrt 3 / 2) * (t * (Real.sqrt 3 / 2))
        = t ^ 2 + (1 - pc γ) * t + (1 - pc γ) ^ 2 := by linear_combination (t ^ 2 / 4) * hs
    rw [e1, e2]
  rw [heq]
  have h0 : 0 ≤ 3 * ε / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ)) := by
    have hγ0 : (0:ℝ) < γ := by linarith
    have : 0 < nu γ := by unfold nu; positivity
    positivity
  exact (part1 γ q hγ).mono (fun t ht => Set.mem_Ici.mpr (le_trans h0 ht.1))

theorem main2 (γ q R : ℝ) (hγ : 1 ≤ γ) :
    StrictAntiOn
      (fun x : ℝ => (-fFn γ q ((pc γ : ℂ) + 2 * pc γ * exp ((2 * Real.pi / 3 : ℝ) * I) - x)).re)
      (Set.Icc 0 R) := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have heq : (fun x : ℝ =>
      (-fFn γ q ((pc γ : ℂ) + 2 * pc γ * exp ((2 * Real.pi / 3 : ℝ) * I) - x)).re)
      = (fun x : ℝ => mu γ * (-x - q)
      - Real.log (x ^ 2 + 3 * pc γ ^ 2) / 2
      + 1 / γ ^ 2 * (Real.log ((1 + x) ^ 2 + 3 * pc γ ^ 2) / 2)) := by
    funext x
    rw [reF]
    have hre : ((pc γ : ℂ) + 2 * pc γ * exp ((2 * Real.pi / 3 : ℝ) * I) - x).re = -x := by
      rw [omega_eq]; simp; ring
    have him : ((pc γ : ℂ) + 2 * pc γ * exp ((2 * Real.pi / 3 : ℝ) * I) - x).im
        = Real.sqrt 3 * pc γ := by
      rw [omega_eq]; simp; ring
    rw [hre, him]
    have e1 : -x * -x + Real.sqrt 3 * pc γ * (Real.sqrt 3 * pc γ) = x ^ 2 + 3 * pc γ ^ 2 := by
      linear_combination (pc γ ^ 2) * hs
    have e2 : (1 - -x) * (1 - -x) + Real.sqrt 3 * pc γ * (Real.sqrt 3 * pc γ)
        = (1 + x) ^ 2 + 3 * pc γ ^ 2 := by
      linear_combination (pc γ ^ 2) * hs
    rw [e1, e2]
  rw [heq]
  exact (part2 γ q hγ).mono (fun x hx => Set.mem_Ici.mpr hx.1)

theorem main3 (γ q R y : ℝ) (hγ : 1 ≤ γ) (hR : 3 ≤ R) :
    (-fFn γ q (-(R : ℂ) + ((Real.sqrt 3 * pc γ - y : ℝ) : ℂ) * I)).re ≤
      (-fFn γ q ((pc γ : ℂ) + 2 * pc γ * exp ((2 * Real.pi / 3 : ℝ) * I))).re := by
  obtain ⟨hp1, hp2, _, _⟩ := pc_facts γ hγ
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [reF, reF]
  have hre1 : (-(R : ℂ) + ((Real.sqrt 3 * pc γ - y : ℝ) : ℂ) * I).re = -R := by simp
  have him1 : (-(R : ℂ) + ((Real.sqrt 3 * pc γ - y : ℝ) : ℂ) * I).im
      = Real.sqrt 3 * pc γ - y := by simp
  have hre2 : ((pc γ : ℂ) + 2 * pc γ * exp ((2 * Real.pi / 3 : ℝ) * I)).re = 0 := by
    rw [omega_eq]; simp; ring
  have him2 : ((pc γ : ℂ) + 2 * pc γ * exp ((2 * Real.pi / 3 : ℝ) * I)).im
      = Real.sqrt 3 * pc γ := by
    rw [omega_eq]; simp; ring
  rw [hre1, him1, hre2, him2]
  set s := Real.sqrt 3 * pc γ - y
  set p := pc γ
  clear_value s p
  have hmu := mu_ge_one γ hγ
  have hc := inv_sq_le_one γ hγ
  have hc0 : 0 ≤ 1 / γ ^ 2 := by positivity
  have ha0 : 0 < -R * -R + s * s := by nlinarith
  have hb1 : 1 ≤ (1 - -R) * (1 - -R) + s * s := by nlinarith
  have hb0 : 0 < (1 - -R) * (1 - -R) + s * s := by linarith
  have hba : Real.log ((1 - -R) * (1 - -R) + s * s) - Real.log (-R * -R + s * s) ≤ 1 := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    have h2 : ((1 - -R) * (1 - -R) + s * s) / (-R * -R + s * s) ≤ 2 := by
      rw [div_le_iff₀ ha0]; nlinarith
    linarith
  have hlb : 0 ≤ Real.log ((1 - -R) * (1 - -R) + s * s) := Real.log_nonneg hb1
  have ht1 : 1 / γ ^ 2 * (Real.log ((1 - -R) * (1 - -R) + s * s) / 2)
      ≤ Real.log ((1 - -R) * (1 - -R) + s * s) / 2 := by
    have := mul_le_of_le_one_left (by linarith : 0 ≤ Real.log ((1 - -R) * (1 - -R) + s * s) / 2) hc
    linarith
  have hd0 : 0 < 0 * 0 + Real.sqrt 3 * p * (Real.sqrt 3 * p) := by
    have : 0 < p := by linarith
    nlinarith
  have hd : Real.log (0 * 0 + Real.sqrt 3 * p * (Real.sqrt 3 * p)) ≤ 2 := by
    have := Real.log_le_sub_one_of_pos hd0
    have : 0 * 0 + Real.sqrt 3 * p * (Real.sqrt 3 * p) = 3 * p ^ 2 := by
      linear_combination (p ^ 2) * hs
    nlinarith
  have he1 : 1 ≤ (1 - 0) * (1 - 0) + Real.sqrt 3 * p * (Real.sqrt 3 * p) := by nlinarith
  have he : 0 ≤ 1 / γ ^ 2 * (Real.log ((1 - 0) * (1 - 0) + Real.sqrt 3 * p * (Real.sqrt 3 * p)) / 2) := by
    have := Real.log_nonneg he1
    positivity
  have hmR : R ≤ mu γ * R := by nlinarith
  have x1 : mu γ * (-R - q) = -(mu γ * R) - mu γ * q := by ring
  have x2 : mu γ * (0 - q) = -(mu γ * q) := by ring
  rw [x1, x2]
  have L1 : -(mu γ * R) - mu γ * q - Real.log (-R * -R + s * s) / 2
      + 1 / γ ^ 2 * (Real.log ((1 - -R) * (1 - -R) + s * s) / 2)
      ≤ -(mu γ * R) - mu γ * q + 1 / 2 := by linarith
  have L2 : -(mu γ * q) - 1 ≤ -(mu γ * q) - Real.log (0 * 0 + Real.sqrt 3 * p * (Real.sqrt 3 * p)) / 2
      + 1 / γ ^ 2 * (Real.log ((1 - 0) * (1 - 0) + Real.sqrt 3 * p * (Real.sqrt 3 * p)) / 2) := by
    generalize Real.log (0 * 0 + Real.sqrt 3 * p * (Real.sqrt 3 * p)) = D at hd ⊢
    generalize 1 / γ ^ 2 * (Real.log ((1 - 0) * (1 - 0) + Real.sqrt 3 * p * (Real.sqrt 3 * p)) / 2) = E at he ⊢
    linarith
  linarith

end SWLem32

open SpikedWishart.SoftEdge Complex in
theorem solution :
    (∀ (γ q ε : ℝ) (M : ℕ), 1 ≤ γ → 0 < ε → 0 < M →
      StrictAntiOn
        (fun t : ℝ => (-fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp ((2 * Real.pi / 3 : ℝ) * I))).re)
        (Set.Icc (3 * ε / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ))) (2 * pc γ))) ∧
    (∀ (γ q R : ℝ), 1 ≤ γ →
      StrictAntiOn
        (fun x : ℝ => (-fFn γ q ((pc γ : ℂ) + 2 * pc γ * exp ((2 * Real.pi / 3 : ℝ) * I) - x)).re)
        (Set.Icc 0 R)) ∧
    (∀ γ₀ : ℝ, 1 ≤ γ₀ → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ (γ q R y : ℝ), 1 ≤ γ → γ ≤ γ₀ → R₀ ≤ R →
      0 ≤ y → y ≤ Real.sqrt 3 * pc γ →
      (-fFn γ q (-(R : ℂ) + ((Real.sqrt 3 * pc γ - y : ℝ) : ℂ) * I)).re ≤
        (-fFn γ q ((pc γ : ℂ) + 2 * pc γ * exp ((2 * Real.pi / 3 : ℝ) * I))).re) := by
  refine ⟨fun γ q ε M hγ hε hM => SWLem32.main1 γ q ε M hγ hε hM,
    fun γ q R hγ => SWLem32.main2 γ q R hγ, fun γ₀ _ => ⟨3, by norm_num, ?_⟩⟩
  intro γ q R y hγ _ hR _ _
  exact SWLem32.main3 γ q R y hγ hR

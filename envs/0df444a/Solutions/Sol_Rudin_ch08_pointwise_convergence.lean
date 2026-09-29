-- Prove2me | solution 1 for Rudin.ch08_pointwise_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T03:49:45.012642+00:00
-- url     : https://prove2.me/submissions/215c9e73-3d8b-41cb-bd9c-882c308decaa

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

open Filter Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators Real FourierTransform
open MeasureTheory Complex

/-!
# Pointwise convergence of Fourier series under a Lipschitz condition (Rudin 8.14)

Mathlib has the `L²` theory of Fourier series on `AddCircle` but no pointwise convergence
criterion.  The Dirichlet kernel and its closed form, the localisation identity, the Dini
quotient with its integrability, and the Riemann-Lebesgue step are all built here, in a
private namespace.
-/

namespace FourierDini


/-- The Dirichlet kernel `D_N(t) = ∑_{n=-N}^{N} e^{i n t}`. -/
noncomputable def dirichlet (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N, Complex.exp ((n : ℂ) * Complex.I * (t : ℂ))

theorem Icc_succ (N : ℕ) :
    Finset.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1)
      = insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) N)) := by
  ext m
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

theorem dirichlet_mul (N : ℕ) (t : ℝ) :
    dirichlet N t * (Complex.exp (Complex.I * t / 2) - Complex.exp (-(Complex.I * t / 2)))
      = Complex.exp (((N : ℂ) + 1 / 2) * Complex.I * t)
        - Complex.exp (-(((N : ℂ) + 1 / 2) * Complex.I * t)) := by
  induction N with
  | zero =>
      simp only [dirichlet, Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton,
        Int.cast_zero, zero_mul, Complex.exp_zero, one_mul, zero_add]
      rw [show (1 / 2 : ℂ) * Complex.I * (t : ℂ) = Complex.I * (t : ℂ) / 2 by ring]
  | succ N ih =>
      have hkey : (Finset.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1)) =
          insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) N)) := Icc_succ N
      have h1 : (-((N : ℤ) + 1)) ∉ insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) N) := by
        simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      have h2 : ((N : ℤ) + 1) ∉ Finset.Icc (-(N : ℤ)) N := by
        simp only [Finset.mem_Icc]; omega
      have hd : dirichlet (N + 1) t
          = Complex.exp ((-((N : ℂ) + 1)) * Complex.I * t)
            + (Complex.exp (((N : ℂ) + 1) * Complex.I * t) + dirichlet N t) := by
        simp only [dirichlet, Nat.cast_add, Nat.cast_one]
        rw [hkey, Finset.sum_insert h1, Finset.sum_insert h2]
        push_cast
        ring_nf
      rw [hd]
      have e1 : Complex.exp ((-((N : ℂ) + 1)) * Complex.I * t)
            * Complex.exp (Complex.I * t / 2)
          = Complex.exp (-(((N : ℂ) + 1 / 2) * Complex.I * t)) := by
        rw [← Complex.exp_add]; congr 1; ring
      have e2 : Complex.exp ((-((N : ℂ) + 1)) * Complex.I * t)
            * Complex.exp (-(Complex.I * t / 2))
          = Complex.exp (-(((N : ℂ) + 1 + 1 / 2) * Complex.I * t)) := by
        rw [← Complex.exp_add]; congr 1; ring
      have e3 : Complex.exp (((N : ℂ) + 1) * Complex.I * t) * Complex.exp (Complex.I * t / 2)
          = Complex.exp (((N : ℂ) + 1 + 1 / 2) * Complex.I * t) := by
        rw [← Complex.exp_add]; congr 1; ring
      have e4 : Complex.exp (((N : ℂ) + 1) * Complex.I * t) * Complex.exp (-(Complex.I * t / 2))
          = Complex.exp (((N : ℂ) + 1 / 2) * Complex.I * t) := by
        rw [← Complex.exp_add]; congr 1; ring
      push_cast
      linear_combination ih + e1 - e2 + e3 - e4

theorem exp_sub_exp (z : ℂ) :
    Complex.exp (Complex.I * z) - Complex.exp (-(Complex.I * z))
      = 2 * Complex.I * Complex.sin z := by
  rw [Complex.sin, mul_comm Complex.I z, show -(z * Complex.I) = -z * Complex.I by ring]
  linear_combination (Complex.exp (z * Complex.I) - Complex.exp (-z * Complex.I))
    * Complex.I_mul_I

/-- Closed form of the Dirichlet kernel: `D_N(t) sin(t/2) = sin((N + 1/2) t)`. -/
theorem dirichlet_mul_sin (N : ℕ) (t : ℝ) :
    dirichlet N t * (Real.sin (t / 2) : ℂ) = (Real.sin (((N : ℝ) + 1 / 2) * t) : ℂ) := by
  have h := dirichlet_mul N t
  have hl : Complex.exp (Complex.I * t / 2) - Complex.exp (-(Complex.I * t / 2))
      = 2 * Complex.I * (Real.sin (t / 2) : ℂ) := by
    have := exp_sub_exp ((t : ℂ) / 2)
    rw [show Complex.I * (t : ℂ) / 2 = Complex.I * ((t : ℂ) / 2) by ring]
    rw [this, show ((t : ℂ) / 2) = (((t / 2 : ℝ) : ℂ)) by push_cast; ring,
      Complex.ofReal_sin]
  have hr : Complex.exp (((N : ℂ) + 1 / 2) * Complex.I * t)
        - Complex.exp (-(((N : ℂ) + 1 / 2) * Complex.I * t))
      = 2 * Complex.I * (Real.sin (((N : ℝ) + 1 / 2) * t) : ℂ) := by
    have := exp_sub_exp ((((N : ℝ) + 1 / 2) * t : ℝ) : ℂ)
    rw [show ((N : ℂ) + 1 / 2) * Complex.I * (t : ℂ)
        = Complex.I * ((((N : ℝ) + 1 / 2) * t : ℝ) : ℂ) by push_cast; ring]
    rw [this, Complex.ofReal_sin]
  rw [hl, hr] at h
  have h2 : (2 : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.I_ne_zero]
  field_simp at h ⊢
  linear_combination h

theorem dirichlet_continuous (N : ℕ) : Continuous (dirichlet N) := by
  refine continuous_finset_sum _ fun n _ => ?_
  exact (Complex.continuous_exp.comp (by fun_prop))

theorem dirichlet_periodic (N : ℕ) : Function.Periodic (dirichlet N) (2 * Real.pi) := by
  intro t
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show ((t + 2 * Real.pi : ℝ) : ℂ) = (t : ℂ) + 2 * (Real.pi : ℂ) by push_cast; ring]
  rw [mul_add, Complex.exp_add]
  rw [show (n : ℂ) * Complex.I * (2 * (Real.pi : ℂ)) = (n : ℂ) * (2 * Real.pi * Complex.I) by ring]
  rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem integral_dirichlet (N : ℕ) :
    (∫ t in (-Real.pi)..Real.pi, dirichlet N t) = 2 * Real.pi := by
  simp only [dirichlet]
  rw [intervalIntegral.integral_finset_sum]
  · have hz : ∀ n ∈ Finset.Icc (-(N : ℤ)) N,
        (∫ t in (-Real.pi)..Real.pi, Complex.exp ((n : ℂ) * Complex.I * (t : ℂ)))
          = if n = 0 then (2 * Real.pi : ℂ) else 0 := by
      intro n _
      by_cases hn : n = 0
      · subst hn
        simp
        ring
      · rw [if_neg hn]
        have hc : ((n : ℂ) * Complex.I) ≠ 0 := by
          simp [hn, Complex.I_ne_zero, Int.cast_eq_zero]
        have := integral_exp_mul_complex (a := -Real.pi) (b := Real.pi) hc
        simp only [mul_assoc] at this ⊢
        rw [this]
        have e1 : Complex.exp ((n : ℂ) * (Complex.I * (Real.pi : ℂ))) = (-1) ^ n := by
          rw [show (n : ℂ) * (Complex.I * (Real.pi : ℂ)) = (n : ℤ) * (Real.pi * Complex.I) by
            push_cast; ring]
          rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
        have hsq : ((-1 : ℂ)) ^ n * ((-1 : ℂ)) ^ n = 1 := by
          rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), show n + n = 2 * n by ring, zpow_mul]
          norm_num
        have e2 : Complex.exp ((n : ℂ) * (Complex.I * ((-Real.pi : ℝ) : ℂ))) = (-1) ^ n := by
          rw [show (n : ℂ) * (Complex.I * ((-Real.pi : ℝ) : ℂ))
              = -((n : ℂ) * (Complex.I * (Real.pi : ℂ))) by push_cast; ring]
          rw [Complex.exp_neg, e1]
          exact inv_eq_of_mul_eq_one_left hsq
        rw [e1, e2, sub_self, zero_div]
    rw [Finset.sum_congr rfl hz]
    rw [Finset.sum_ite_eq' (Finset.Icc (-(N : ℤ)) N) (0 : ℤ) (fun _ => (2 * Real.pi : ℂ))]
    rw [if_pos (by simp [Finset.mem_Icc])]
  · intro n _
    exact (Complex.continuous_exp.comp (by fun_prop)).intervalIntegrable _ _

/-! ## Riemann–Lebesgue on `[-π, π]` -/

theorem tendsto_cocompact_lin {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun N : ℕ => c * N) atTop (cocompact ℝ) := by
  rw [cocompact_eq_atBot_atTop]
  have base : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  rcases lt_or_gt_of_ne hc with h | h
  · exact Tendsto.mono_right (Filter.Tendsto.const_mul_atTop_of_neg h base) le_sup_left
  · exact Tendsto.mono_right (Filter.Tendsto.const_mul_atTop h base) le_sup_right

/-- The Riemann–Lebesgue lemma on `[-π, π]`, in the form needed below. -/
theorem riemann_lebesgue (h : ℝ → ℂ) {σ : ℝ} (hσ : σ ≠ 0) :
    Tendsto (fun N : ℕ => ∫ t in (-Real.pi)..Real.pi,
        h t * Complex.exp (Complex.I * ((σ * N * t : ℝ) : ℂ))) atTop (𝓝 0) := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  set H : ℝ → ℂ := Set.indicator (Set.Ioc (-Real.pi) Real.pi) h with hHdef
  have hw : Tendsto (fun N : ℕ => (-σ / (2 * Real.pi)) * N) atTop (cocompact ℝ) :=
    tendsto_cocompact_lin (by
      simp only [ne_eq, div_eq_zero_iff, neg_eq_zero]
      push Not
      exact ⟨hσ, hpi⟩)
  have key := (Real.zero_at_infty_fourier H).comp hw
  refine key.congr fun N => ?_
  show 𝓕 H ((-σ / (2 * Real.pi)) * N) = _
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hexp : ∀ v : ℝ, ((-2 * Real.pi * v * ((-σ / (2 * Real.pi)) * N) : ℝ) : ℂ) * Complex.I
      = Complex.I * ((σ * N * v : ℝ) : ℂ) := by
    intro v
    have : (-2 * Real.pi * v * ((-σ / (2 * Real.pi)) * N)) = σ * N * v := by
      field_simp
    rw [this]
    ring
  simp only [hexp, smul_eq_mul]
  have hind : ∀ v : ℝ, Complex.exp (Complex.I * ((σ * N * v : ℝ) : ℂ)) * H v
      = Set.indicator (Set.Ioc (-Real.pi) Real.pi)
          (fun v => h v * Complex.exp (Complex.I * ((σ * N * v : ℝ) : ℂ))) v := by
    intro v
    by_cases hv : v ∈ Set.Ioc (-Real.pi) Real.pi
    · simp [hHdef, Set.indicator_of_mem hv, mul_comm]
    · simp [hHdef, Set.indicator_of_notMem hv]
  simp only [hind]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]

theorem intble_exp {h : ℝ → ℂ} (hh : IntervalIntegrable h volume (-Real.pi) Real.pi)
    (σ : ℝ) (N : ℕ) :
    IntervalIntegrable (fun t => h t * Complex.exp (Complex.I * ((σ * N * t : ℝ) : ℂ)))
      volume (-Real.pi) Real.pi :=
  hh.mul_continuousOn (by fun_prop)

theorem rl_sin {h : ℝ → ℂ} (hh : IntervalIntegrable h volume (-Real.pi) Real.pi) :
    Tendsto (fun N : ℕ => ∫ t in (-Real.pi)..Real.pi, h t * (Real.sin ((N : ℝ) * t) : ℂ))
      atTop (𝓝 0) := by
  have h1 := riemann_lebesgue h (σ := 1) one_ne_zero
  have h2 := riemann_lebesgue h (σ := -1) (by norm_num)
  have key := (h2.const_mul (Complex.I / 2)).sub (h1.const_mul (Complex.I / 2))
  rw [mul_zero, sub_zero] at key
  refine key.congr fun N => ?_
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub ((intble_exp hh (-1) N).const_mul _)
      ((intble_exp hh 1 N).const_mul _)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Complex.ofReal_sin, Complex.sin]
  push_cast
  ring_nf

theorem rl_cos {h : ℝ → ℂ} (hh : IntervalIntegrable h volume (-Real.pi) Real.pi) :
    Tendsto (fun N : ℕ => ∫ t in (-Real.pi)..Real.pi, h t * (Real.cos ((N : ℝ) * t) : ℂ))
      atTop (𝓝 0) := by
  have h1 := riemann_lebesgue h (σ := 1) one_ne_zero
  have h2 := riemann_lebesgue h (σ := -1) (by norm_num)
  have key := (h2.const_mul ((1 : ℂ) / 2)).add (h1.const_mul ((1 : ℂ) / 2))
  rw [mul_zero, add_zero] at key
  refine key.congr fun N => ?_
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((intble_exp hh (-1) N).const_mul _)
      ((intble_exp hh 1 N).const_mul _)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-! ## The localisation identity -/

section Loc

variable {f : ℝ → ℂ}

theorem intble_all (hper : Function.Periodic f (2 * Real.pi))
    (hint : IntervalIntegrable f volume (-Real.pi) Real.pi) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  refine hper.intervalIntegrable (t := -Real.pi) (by positivity) ?_ a b
  have : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [this]
  exact hint

theorem partialSum_eq (hint : IntervalIntegrable f volume (-Real.pi) Real.pi) (N : ℕ) (x : ℝ) :
    Rudin.fourierPartialSum f N x
      = (1 / (2 * Real.pi) : ℂ) * ∫ y in (-Real.pi)..Real.pi, f y * dirichlet N (x - y) := by
  have hstep : ∀ n : ℤ,
      (∫ y in (-Real.pi)..Real.pi, f y * Complex.exp (-(n : ℂ) * Complex.I * (y : ℂ)))
          * Complex.exp ((n : ℂ) * Complex.I * (x : ℂ))
        = ∫ y in (-Real.pi)..Real.pi,
            f y * Complex.exp ((n : ℂ) * Complex.I * ((x - y : ℝ) : ℂ)) := by
    intro n
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  simp only [Rudin.fourierPartialSum, Rudin.fourierCoeff, dirichlet]
  rw [intervalIntegral.integral_congr
    (g := fun y => ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
      f y * Complex.exp ((n : ℂ) * Complex.I * ((x - y : ℝ) : ℂ)))
    (fun y _ => Finset.mul_sum _ _ _)]
  rw [intervalIntegral.integral_finset_sum
    (fun n _ => hint.mul_continuousOn (by fun_prop))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_assoc, hstep n]

theorem conv_shift (hper : Function.Periodic f (2 * Real.pi)) (N : ℕ) (x : ℝ) :
    (∫ y in (-Real.pi)..Real.pi, f y * dirichlet N (x - y))
      = ∫ t in (-Real.pi)..Real.pi, f (x - t) * dirichlet N t := by
  have hP : Function.Periodic (fun y => f y * dirichlet N (x - y)) (2 * Real.pi) := by
    intro y
    have h1 : f (y + 2 * Real.pi) = f y := hper y
    have h2 : dirichlet N (x - (y + 2 * Real.pi)) = dirichlet N (x - y) := by
      have : x - (y + 2 * Real.pi) = (x - y) - 2 * Real.pi := by ring
      rw [this, (dirichlet_periodic N).sub_eq]
    show f (y + 2 * Real.pi) * dirichlet N (x - (y + 2 * Real.pi))
        = f y * dirichlet N (x - y)
    rw [h1, h2]
  have hcv := intervalIntegral.integral_comp_sub_left
    (a := -Real.pi) (b := Real.pi) (fun y => f y * dirichlet N (x - y)) x
  have hsimp : (fun t : ℝ => f (x - t) * dirichlet N (x - (x - t)))
      = fun t : ℝ => f (x - t) * dirichlet N t := by
    funext t; congr 2; ring
  rw [hsimp] at hcv
  rw [hcv, show x - -Real.pi = x + Real.pi by ring]
  have e1 : x - Real.pi + 2 * Real.pi = x + Real.pi := by ring
  have e2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have := hP.intervalIntegral_add_eq (x - Real.pi) (-Real.pi)
  rw [e1, e2] at this
  exact this.symm

theorem localization (hper : Function.Periodic f (2 * Real.pi))
    (hint : IntervalIntegrable f volume (-Real.pi) Real.pi) (N : ℕ) (x : ℝ) :
    Rudin.fourierPartialSum f N x - f x
      = (1 / (2 * Real.pi) : ℂ)
        * ∫ t in (-Real.pi)..Real.pi, (f (x - t) - f x) * dirichlet N t := by
  have hrefl : IntervalIntegrable (fun t => f (x - t)) volume (-Real.pi) Real.pi := by
    have h0 : IntervalIntegrable f volume (x - Real.pi) (x + Real.pi) :=
      intble_all hper hint _ _
    have := h0.comp_sub_left x
    have e1 : x - (x + Real.pi) = -Real.pi := by ring
    have e2 : x - (x - Real.pi) = Real.pi := by ring
    rw [e1, e2] at this
    exact this.symm
  have hA : IntervalIntegrable (fun t => f (x - t) * dirichlet N t) volume (-Real.pi) Real.pi :=
    hrefl.mul_continuousOn (dirichlet_continuous N).continuousOn
  have hB : IntervalIntegrable (fun t => f x * dirichlet N t) volume (-Real.pi) Real.pi :=
    ((dirichlet_continuous N).const_smul (f x)).intervalIntegrable _ _
  rw [partialSum_eq hint N x, conv_shift hper N x]
  have hsplit : (∫ t in (-Real.pi)..Real.pi, (f (x - t) - f x) * dirichlet N t)
      = (∫ t in (-Real.pi)..Real.pi, f (x - t) * dirichlet N t)
        - ∫ t in (-Real.pi)..Real.pi, f x * dirichlet N t := by
    rw [← intervalIntegral.integral_sub hA hB]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  rw [hsplit, intervalIntegral.integral_const_mul, integral_dirichlet]
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero]
  field_simp

end Loc

/-! ## The Dini quotient -/

section Dini

variable {f : ℝ → ℂ} {x : ℝ}

/-- The quotient `(f(x - t) - f x) / sin(t/2)` occurring in the Dini test; it is `0` at `t = 0`
because division by zero is `0`. -/
noncomputable def quot (f : ℝ → ℂ) (x : ℝ) (t : ℝ) : ℂ :=
  (f (x - t) - f x) / (Real.sin (t / 2) : ℂ)

theorem sin_half_ne_zero {t : ℝ} (ht : t ∈ Set.Icc (-Real.pi) Real.pi) (ht0 : t ≠ 0) :
    Real.sin (t / 2) ≠ 0 := by
  obtain ⟨h1, h2⟩ := ht
  have hpi := Real.pi_pos
  intro hc
  rcases (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith)).1 hc with h
  exact ht0 (by linarith)

theorem quot_mul_sin (f : ℝ → ℂ) (x : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
    quot f x t * (Real.sin (t / 2) : ℂ) = f (x - t) - f x := by
  by_cases ht0 : t = 0
  · subst ht0
    simp [quot]
  · rw [quot, div_mul_cancel₀]
    exact_mod_cast Complex.ofReal_ne_zero.2 (sin_half_ne_zero ht ht0)

theorem kernel_split (f : ℝ → ℂ) (x : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (-Real.pi) Real.pi) (N : ℕ) :
    (f (x - t) - f x) * dirichlet N t
      = (quot f x t * (Real.cos (t / 2) : ℂ)) * (Real.sin ((N : ℝ) * t) : ℂ)
        + (f (x - t) - f x) * (Real.cos ((N : ℝ) * t) : ℂ) := by
  have hsplit : Real.sin (((N : ℝ) + 1 / 2) * t)
      = Real.sin ((N : ℝ) * t) * Real.cos (t / 2) + Real.cos ((N : ℝ) * t) * Real.sin (t / 2) := by
    rw [show ((N : ℝ) + 1 / 2) * t = (N : ℝ) * t + t / 2 by ring, Real.sin_add]
  have hq : quot f x t * ((dirichlet N t) * (Real.sin (t / 2) : ℂ))
      = (f (x - t) - f x) * dirichlet N t := by
    rw [← mul_assoc, mul_comm (quot f x t) (dirichlet N t), mul_assoc, quot_mul_sin f x ht]
    ring
  rw [← hq, dirichlet_mul_sin, hsplit]
  push_cast
  rw [← quot_mul_sin f x ht]
  simp only [Complex.ofReal_sin, Complex.ofReal_cos]
  push_cast
  ring

theorem abs_sin_half {t : ℝ} (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
    |Real.sin (t / 2)| = Real.sin (|t| / 2) := by
  obtain ⟨h1, h2⟩ := ht
  have hpi := Real.pi_pos
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith))]
  · have hs : Real.sin (-(t / 2)) ≥ 0 :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [Real.sin_neg] at hs
    rw [abs_of_neg h, abs_of_nonpos (by linarith), neg_div, Real.sin_neg]

theorem sin_half_ge {d t : ℝ} (hd : 0 < d) (hdpi : d ≤ Real.pi)
    (ht : t ∈ Set.Icc (-Real.pi) Real.pi) (hdt : d ≤ |t|) :
    Real.sin (d / 2) ≤ |Real.sin (t / 2)| := by
  have hpi := Real.pi_pos
  rw [abs_sin_half ht]
  have h1 : d / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> [linarith; linarith]
  have h2 : |t| / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    have := abs_le.1 (abs_le.2 ⟨ht.1, ht.2⟩)
    constructor
    · have : (0 : ℝ) ≤ |t| := abs_nonneg t
      linarith
    · have : |t| ≤ Real.pi := abs_le.2 ⟨ht.1, ht.2⟩
      linarith
  exact Real.strictMonoOn_sin.monotoneOn h1 h2 (by linarith)

/-- The Dini quotient is integrable on `[-π, π]` under a one-sided Lipschitz bound at `x`. -/
theorem quot_intble (hper : Function.Periodic f (2 * Real.pi))
    (hint : IntervalIntegrable f volume (-Real.pi) Real.pi)
    {δ M : ℝ} (hδ : 0 < δ)
    (hlip : ∀ t : ℝ, |t| < δ → ‖f (x + t) - f x‖ ≤ M * |t|) :
    IntervalIntegrable (quot f x) volume (-Real.pi) Real.pi := by
  have hpi := Real.pi_pos
  have hpile : -Real.pi ≤ Real.pi := by linarith
  -- the numerator is integrable
  have hrefl : IntervalIntegrable (fun t => f (x - t)) volume (-Real.pi) Real.pi := by
    have h0 : IntervalIntegrable f volume (x - Real.pi) (x + Real.pi) := intble_all hper hint _ _
    have h1 := h0.comp_sub_left x
    rw [show x - (x + Real.pi) = -Real.pi by ring, show x - (x - Real.pi) = Real.pi by ring] at h1
    exact h1.symm
  have hnum : IntervalIntegrable (fun t => f (x - t) - f x) volume (-Real.pi) Real.pi :=
    hrefl.sub (intervalIntegrable_const)
  -- constants
  set d : ℝ := min (δ / 2) Real.pi with hd_def
  have hd0 : 0 < d := lt_min (by linarith) hpi
  have hdpi : d ≤ Real.pi := min_le_right _ _
  have hdδ : d < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hM : 0 ≤ M := by
    have h := hlip (δ / 2) (by rw [abs_of_pos (by linarith)]; linarith)
    have h2 : (0 : ℝ) ≤ M * |δ / 2| := le_trans (norm_nonneg _) h
    rw [abs_of_pos (by linarith : (0:ℝ) < δ / 2)] at h2
    nlinarith
  set c : ℝ := Real.sin (d / 2) with hc_def
  have hc0 : 0 < c := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  -- the dominating function
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpile] at hnum ⊢
  have hdom : IntegrableOn (fun t : ℝ => M * Real.pi + ‖f (x - t) - f x‖ / c)
      (Set.Ioc (-Real.pi) Real.pi) volume :=
    (continuous_const.integrableOn_Ioc).add (hnum.norm.div_const c)
  refine hdom.mono' ?_ ?_
  · -- measurability
    have h1 : AEStronglyMeasurable (fun t : ℝ => f (x - t) - f x)
        (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) := hnum.aestronglyMeasurable
    have h2 : Measurable (fun t : ℝ => ((Real.sin (t / 2) : ℝ) : ℂ)⁻¹) := by
      fun_prop
    exact h1.mul h2.aestronglyMeasurable
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc ?_
    intro t htm
    have ht : t ∈ Set.Icc (-Real.pi) Real.pi := ⟨le_of_lt htm.1, htm.2⟩
    have habs : ‖quot f x t‖ = ‖f (x - t) - f x‖ / |Real.sin (t / 2)| := by
      rw [quot, norm_div, Complex.norm_real, Real.norm_eq_abs]
    rcases le_or_gt |t| d with hsmall | hbig
    · by_cases ht0 : t = 0
      · subst ht0
        have h0 : quot f x 0 = 0 := by simp [quot]
        rw [h0, norm_zero]
        have h1 : 0 ≤ ‖f (x - (0:ℝ)) - f x‖ / c := by positivity
        nlinarith [mul_nonneg hM hpi.le]
      · have hta : 0 < |t| := abs_pos.2 ht0
        have hlip' : ‖f (x - t) - f x‖ ≤ M * |t| := by
          have h := hlip (-t) (by rw [abs_neg]; linarith)
          rwa [show x + -t = x - t by ring, abs_neg] at h
        have hle : |t / 2| ≤ Real.pi / 2 := by
          rw [abs_div]
          have : |t| ≤ Real.pi := abs_le.2 ⟨ht.1, ht.2⟩
          simp only [Nat.abs_ofNat]
          linarith
        have hjordan : 2 / Real.pi * |t / 2| ≤ |Real.sin (t / 2)| := Real.mul_abs_le_abs_sin hle
        have hj : |t| / Real.pi ≤ |Real.sin (t / 2)| := by
          rw [abs_div] at hjordan
          simp only [Nat.abs_ofNat] at hjordan
          rw [div_le_iff₀ hpi]
          have hmul := mul_le_mul_of_nonneg_right hjordan hpi.le
          have e : (2 / Real.pi * (|t| / 2)) * Real.pi = |t| := by field_simp
          rw [e] at hmul
          exact hmul
        have hb : 0 < |Real.sin (t / 2)| := lt_of_lt_of_le (by positivity) hj
        have hkey : ‖f (x - t) - f x‖ / |Real.sin (t / 2)| ≤ M * Real.pi := by
          rw [div_le_iff₀ hb]
          have h2 : |t| ≤ Real.pi * |Real.sin (t / 2)| := by
            rw [div_le_iff₀ hpi] at hj; linarith [hj]
          nlinarith [mul_nonneg hM (sub_nonneg.2 h2)]
        have h3 : 0 ≤ ‖f (x - t) - f x‖ / c := by positivity
        rw [habs]
        linarith
    · have hcb : c ≤ |Real.sin (t / 2)| := sin_half_ge hd0 hdpi ht (le_of_lt hbig)
      have hb : 0 < |Real.sin (t / 2)| := lt_of_lt_of_le hc0 hcb
      have h1 : ‖f (x - t) - f x‖ / |Real.sin (t / 2)| ≤ ‖f (x - t) - f x‖ / c := by
        rw [div_le_div_iff₀ hb hc0]
        nlinarith [norm_nonneg (f (x - t) - f x)]
      rw [habs]
      nlinarith [mul_nonneg hM hpi.le]

theorem num_intble (hper : Function.Periodic f (2 * Real.pi))
    (hint : IntervalIntegrable f volume (-Real.pi) Real.pi) :
    IntervalIntegrable (fun t => f (x - t) - f x) volume (-Real.pi) Real.pi := by
  have h0 : IntervalIntegrable f volume (x - Real.pi) (x + Real.pi) := intble_all hper hint _ _
  have h1 := h0.comp_sub_left x
  rw [show x - (x + Real.pi) = -Real.pi by ring, show x - (x - Real.pi) = Real.pi by ring] at h1
  exact h1.symm.sub intervalIntegrable_const

/-- **Rudin, Theorem 8.14.**  If `f` satisfies a Lipschitz bound at `x`, its Fourier series
converges to `f x` there. -/
theorem tendsto_fourierPartialSum (hper : Function.Periodic f (2 * Real.pi))
    (hint : IntervalIntegrable f volume (-Real.pi) Real.pi)
    {δ M : ℝ} (hδ : 0 < δ)
    (hlip : ∀ t : ℝ, |t| < δ → ‖f (x + t) - f x‖ ≤ M * |t|) :
    Tendsto (fun N => Rudin.fourierPartialSum f N x) atTop (𝓝 (f x)) := by
  have hpi := Real.pi_pos
  have hpile : -Real.pi ≤ Real.pi := by linarith
  have hq := quot_intble hper hint hδ hlip
  have hA : IntervalIntegrable (fun t => quot f x t * (Real.cos (t / 2) : ℂ))
      volume (-Real.pi) Real.pi := hq.mul_continuousOn (by fun_prop)
  have hnum := num_intble (f := f) (x := x) hper hint
  have hsplit : ∀ N : ℕ,
      (∫ t in (-Real.pi)..Real.pi, (f (x - t) - f x) * dirichlet N t)
        = (∫ t in (-Real.pi)..Real.pi,
              (quot f x t * (Real.cos (t / 2) : ℂ)) * (Real.sin ((N : ℝ) * t) : ℂ))
          + ∫ t in (-Real.pi)..Real.pi, (f (x - t) - f x) * (Real.cos ((N : ℝ) * t) : ℂ) := by
    intro N
    rw [← intervalIntegral.integral_add (hA.mul_continuousOn (by fun_prop))
      (hnum.mul_continuousOn (by fun_prop))]
    refine intervalIntegral.integral_congr fun t htu => ?_
    exact kernel_split f x (by rwa [Set.uIcc_of_le hpile] at htu) N
  have hlim : Tendsto (fun N : ℕ => Rudin.fourierPartialSum f N x - f x) atTop (𝓝 0) := by
    have h1 := rl_sin hA
    have h2 := rl_cos hnum
    have h3 := (h1.add h2).const_mul ((1 / (2 * Real.pi) : ℂ))
    rw [add_zero, mul_zero] at h3
    refine h3.congr fun N => ?_
    rw [← hsplit N, ← localization hper hint N x]
  rwa [tendsto_sub_nhds_zero_iff] at hlim

end Dini


end FourierDini

open Filter Topology in
theorem solution (f : ℝ → ℂ) (hper : Rudin.HasPeriodTwoPi f)
    (hint : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (x : ℝ) (δ M : ℝ) (hδ : 0 < δ)
    (hlip : ∀ t : ℝ, |t| < δ → ‖f (x + t) - f x‖ ≤ M * |t|) :
    Tendsto (fun N => Rudin.fourierPartialSum f N x) atTop (𝓝 (f x)) :=
  FourierDini.tendsto_fourierPartialSum (fun y => hper y) hint hδ hlip

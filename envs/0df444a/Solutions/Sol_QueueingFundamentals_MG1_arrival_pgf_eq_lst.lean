-- Prove2me | solution 1 for QueueingFundamentals.MG1.arrival_pgf_eq_lst
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T00:26:23.325422+00:00
-- url     : https://prove2.me/submissions/d4309bd8-7be1-4549-b5a0-1b11dccad14f

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain
import Definitions.Def_QueueingFundamentals_MG1_transforms

open MeasureTheory in
theorem eeaf49a0_hasSum_pt (lam t : ℝ) (z : ℂ) :
    HasSum (fun n : ℕ => (((Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ) : ℝ)) : ℂ) * z ^ n)
      (Complex.exp (-((lam : ℂ) * (1 - z) * (t : ℂ)))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (((lam * t : ℝ) : ℂ) * z)).mul_left
    ((Real.exp (-(lam * t)) : ℝ) : ℂ)
  rw [← Complex.exp_eq_exp_ℂ] at h
  have he : ((Real.exp (-(lam * t)) : ℝ) : ℂ) * Complex.exp (((lam * t : ℝ) : ℂ) * z)
      = Complex.exp (-((lam : ℂ) * (1 - z) * (t : ℂ))) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast; ring
  rw [he] at h
  have hf : (fun n : ℕ => (((Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ) : ℝ)) : ℂ) * z ^ n)
      = (fun i : ℕ => ((Real.exp (-(lam * t)) : ℝ) : ℂ) * ((((lam * t : ℝ) : ℂ) * z) ^ i / (i.factorial : ℂ))) := by
    funext n
    push_cast
    rw [mul_pow]
    ring
  rw [hf]; exact h

open MeasureTheory in
theorem eeaf49a0_bound_tsum (lam t : ℝ) (ht : 0 ≤ t) (hlam : 0 < lam) :
    ∑' n : ℕ, |Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ)| = 1 := by
  have hx : 0 ≤ lam * t := mul_nonneg hlam.le ht
  have h1 : ∀ n : ℕ, |Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ)|
      = Real.exp (-(lam * t)) * ((lam * t) ^ n / (Nat.factorial n : ℝ)) := by
    intro n
    rw [abs_of_nonneg (by positivity)]
    ring
  simp_rw [h1]
  rw [tsum_mul_left]
  have h2 := NormedSpace.expSeries_div_hasSum_exp (lam * t)
  rw [← Real.exp_eq_exp_ℝ] at h2
  rw [h2.tsum_eq, ← Real.exp_add]
  simp

open MeasureTheory in
theorem eeaf49a0_ae_nonneg (B : Measure ℝ) (hB : B (Set.Iio 0) = 0) : ∀ᵐ t ∂B, 0 ≤ t := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext a; simp
  rw [this]; exact hB

open QueueingFundamentals.MG1 MeasureTheory in
theorem solution (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    pgf (arrivalProb lam B) z = lst B ((lam : ℂ) * (1 - z)) := by
  have hae := eeaf49a0_ae_nonneg B hB
  have key := hasSum_integral_of_dominated_convergence (μ := B)
    (F := fun (n : ℕ) (t : ℝ) =>
      (((Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ) : ℝ)) : ℂ) * z ^ n)
    (f := fun t : ℝ => Complex.exp (-((lam : ℂ) * (1 - z) * (t : ℂ))))
    (fun n t => |Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ)|)
    (fun n => by
      apply Continuous.aestronglyMeasurable
      fun_prop)
    (fun n => Filter.Eventually.of_forall (fun t => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
      calc _ ≤ |Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ)| * 1 := by
            gcongr
            exact pow_le_one₀ (norm_nonneg _) hz
        _ = _ := mul_one _))
    (Filter.Eventually.of_forall (fun t =>
      ((Real.summable_pow_div_factorial (lam * t)).mul_left (Real.exp (-(lam * t)))).abs.congr
        (fun n => by ring_nf)))
    ((integrable_const (1 : ℝ)).congr (hae.mono fun t ht => (eeaf49a0_bound_tsum lam t ht hlam).symm))
    (Filter.Eventually.of_forall (fun t => eeaf49a0_hasSum_pt lam t z))
  unfold pgf lst
  convert key.tsum_eq using 1
  · congr 1
    funext n
    unfold arrivalProb
    rw [integral_mul_const, integral_complex_ofReal]

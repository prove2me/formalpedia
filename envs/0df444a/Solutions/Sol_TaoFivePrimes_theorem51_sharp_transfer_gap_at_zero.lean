-- Prove2me | solution 1 for TaoFivePrimes.theorem51_sharp_transfer_gap_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-22T20:57:17.617191+00:00
-- url     : https://prove2.me/submissions/330f688a-1272-43d2-997b-3c60dff9fe6f

import Definitions.Def_TaoFivePrimes_TypeISlabSums

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction Finset

namespace TaoFivePrimes

open TypeIOuterDAssembly

/-! ## The sharp transfer gap at `α = 0` (elementary positivity case)

At `α = 0` the exponential test function `eta0VaughanTest x 0 n` is a nonnegative
real, so every slab sum is a nonnegative real (as a complex number) and the sharp
transfer gap follows from positivity, `|μ d| ≤ 1`, the coefficient bound
`|f_d| ≤ log d`, and `transferredInnerSupport ⊆ fullInnerSupport`. -/

private lemma eta0_nonneg (t : ℝ) : 0 ≤ eta0 t := by
  rw [eta0]
  split <;> positivity

private lemma eta0VaughanTest_zero (x : ℝ) (n : ℕ) :
    eta0VaughanTest x 0 n = ((if n.Coprime 2 then eta0 ((n : ℝ) / x) else 0 : ℝ) : ℂ) := by
  simp only [eta0VaughanTest, expCircle, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_mul]
  split <;> simp

private lemma testReal_nonneg {x : ℝ} {n : ℕ} :
    0 ≤ (if n.Coprime 2 then eta0 ((n : ℝ) / x) else 0 : ℝ) := by
  split
  · exact eta0_nonneg _
  · exact le_refl 0

private lemma testReal_zero {x : ℝ} {n : ℕ} (hn : ¬ n.Coprime 2) :
    (if n.Coprime 2 then eta0 ((n : ℝ) / x) else 0 : ℝ) = 0 := if_neg hn

/-- The `S1` slab at `α = 0`, as a real number. -/
private noncomputable def s1R (x : ℝ) (d : ℕ) : ℝ :=
  ∑ w ∈ fullInnerSupport x d, Real.log (w : ℝ) * eta0 (((d * w : ℕ) : ℝ) / x)

/-- The `S0` slab at `α = 0`, as a real number. -/
private noncomputable def s0R (x : ℝ) (d : ℕ) : ℝ :=
  ∑ w ∈ fullInnerSupport x d, eta0 (((d * w : ℕ) : ℝ) / x)

/-- The `K` slab at `α = 0`, as a real number. -/
private noncomputable def kR (x V : ℝ) (d : ℕ) : ℝ :=
  ∑ w ∈ transferredInnerSupport x V d, Real.log (w : ℝ) * eta0 (((d * w : ℕ) : ℝ) / x)

private lemma mem_fullInnerSupport_spec {x : ℝ} {d w : ℕ} (hw : w ∈ fullInnerSupport x d) :
    (d, w) ∈ eta0VaughanOpenOddPairs x := (Finset.mem_filter.mp hw).2

private lemma coprime_two_mul {d w : ℕ} (hd : d.Coprime 2) (hw : w.Coprime 2) :
    (d * w).Coprime 2 := Nat.Coprime.mul_left hd hw

private lemma fullInnerSupport_coprime {x : ℝ} {d w : ℕ} (hw : w ∈ fullInnerSupport x d) :
    (d * w).Coprime 2 := by
  have hpair := (Finset.mem_filter.mp (mem_fullInnerSupport_spec hw)).2
  exact coprime_two_mul hpair.2.1 hpair.2.2.1

private lemma fullInnerSupport_pos {x : ℝ} {d w : ℕ} (hw : w ∈ fullInnerSupport x d) :
    0 < w := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hw).1).1

private lemma fullInnerSupport_log_nonneg {x : ℝ} {d w : ℕ}
    (hw : w ∈ fullInnerSupport x d) : 0 ≤ Real.log (w : ℝ) := by
  apply Real.log_nonneg
  have h1 : (1 : ℕ) ≤ w :=
    Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (fullInnerSupport_pos hw))
  exact_mod_cast h1

private lemma s1R_nonneg (x : ℝ) (d : ℕ) : 0 ≤ s1R x d := by
  unfold s1R
  exact Finset.sum_nonneg fun w hw =>
    mul_nonneg (fullInnerSupport_log_nonneg hw) (eta0_nonneg _)

private lemma s0R_nonneg (x : ℝ) (d : ℕ) : 0 ≤ s0R x d := by
  unfold s0R
  exact Finset.sum_nonneg fun w _ => eta0_nonneg _

private lemma typeISlabS1_zero (x : ℝ) (d : ℕ) :
    typeISlabS1 x 0 d = ((s1R x d : ℝ) : ℂ) := by
  unfold typeISlabS1 s1R
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [eta0VaughanTest_zero, if_pos (fullInnerSupport_coprime hw)]
  push_cast
  ring

private lemma typeISlabS0_zero (x : ℝ) (d : ℕ) :
    typeISlabS0 x 0 d = ((s0R x d : ℝ) : ℂ) := by
  unfold typeISlabS0 s0R
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [eta0VaughanTest_zero, if_pos (fullInnerSupport_coprime hw)]

private lemma typeISlabK_zero (x V : ℝ) (d : ℕ) :
    typeISlabK x 0 V d = ((kR x V d : ℝ) : ℂ) := by
  unfold typeISlabK kR
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hfull : w ∈ fullInnerSupport x d := Finset.mem_filter.mp hw |>.1
  rw [eta0VaughanTest_zero, if_pos (fullInnerSupport_coprime hfull)]
  push_cast
  ring

private lemma kR_nonneg (x V : ℝ) (d : ℕ) : 0 ≤ kR x V d := by
  unfold kR
  exact Finset.sum_nonneg fun w hw =>
    mul_nonneg (fullInnerSupport_log_nonneg (Finset.mem_filter.mp hw).1) (eta0_nonneg _)

private lemma kR_le_s1R (x V : ℝ) (d : ℕ) : kR x V d ≤ s1R x d := by
  unfold kR s1R transferredInnerSupport
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro w hwfull _hwnot
  exact mul_nonneg (fullInnerSupport_log_nonneg hwfull) (eta0_nonneg _)

private lemma norm_typeISlabS1_zero (x : ℝ) (d : ℕ) :
    ‖typeISlabS1 x 0 d‖ = s1R x d := by
  rw [typeISlabS1_zero, Complex.norm_of_nonneg (s1R_nonneg x d)]

private lemma norm_typeISlabS0_zero (x : ℝ) (d : ℕ) :
    ‖typeISlabS0 x 0 d‖ = s0R x d := by
  rw [typeISlabS0_zero, Complex.norm_of_nonneg (s0R_nonneg x d)]

private lemma norm_moebius_intCast_le_one (d : ℕ) :
    ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
  have h0 : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
  have h1 : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast h0
  simpa using h1

private lemma norm_moebius_if_le_one (U : ℝ) (d : ℕ) :
    ‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖ ≤ 1 := by
  split
  · exact norm_moebius_intCast_le_one d
  · simp

private lemma arithmeticRestrictLE_apply (B : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    arithmeticRestrictLE B f n = if n ≤ B then f n else 0 := rfl

/-- The coefficient bound `|f_d| ≤ log d` for the Vaughan Type I correction coefficient. -/
private lemma coeff_le_log (U V : ℝ) (d : ℕ) :
    |vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d| ≤ Real.log d := by
  rw [vaughanTypeICorrectionCoefficient, ArithmeticFunction.mul_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ d.divisorsAntidiagonal,
      |arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) p.1 *
          arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt p.2|
        ≤ ArithmeticFunction.vonMangoldt p.2 := by
    rintro ⟨a, b⟩ _hp
    have hmu : |arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) a| ≤ 1 := by
      have h0 : |(ArithmeticFunction.moebius a : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
      have h1 : |((ArithmeticFunction.moebius a : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast h0
      rw [arithmeticRestrictLE_apply]
      split
      · simpa using h1
      · norm_num
    have hvm0 : 0 ≤ ArithmeticFunction.vonMangoldt b := ArithmeticFunction.vonMangoldt_nonneg
    have hvm : |arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt b|
        ≤ ArithmeticFunction.vonMangoldt b := by
      rw [arithmeticRestrictLE_apply]
      split
      · exact le_of_eq (abs_of_nonneg hvm0)
      · simpa using hvm0
    calc |arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) a *
            arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt b|
        = |arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) a| *
            |arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt b| := abs_mul _ _
      _ ≤ 1 * ArithmeticFunction.vonMangoldt b :=
          mul_le_mul hmu hvm (abs_nonneg _) (by norm_num)
      _ = ArithmeticFunction.vonMangoldt b := one_mul _
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hz : (ArithmeticFunction.zeta * ArithmeticFunction.vonMangoldt) d = Real.log d := by
      rw [ArithmeticFunction.zeta_mul_vonMangoldt, ArithmeticFunction.log_apply]
    rw [ArithmeticFunction.mul_apply] at hz
    have hz' : ∑ p ∈ d.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt p.2 = Real.log d := by
      rw [← hz]
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 : p.1 ≠ 0 := by
        intro h0
        have h1 := (Nat.mem_divisorsAntidiagonal.mp hp).1
        rw [h0, zero_mul] at h1
        omega
      simp [ArithmeticFunction.zeta_apply, hp0]
    exact le_of_eq hz'

private lemma term1_le (x U V : ℝ) :
    (∑ d ∈ theorem51Divisors U V,
        ‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖ *
          ‖typeISlabS1 x 0 d‖)
      ≤ ∑ d ∈ (theorem51Divisors U V).filter (fun d => d ≤ ⌊U⌋₊), s1R x d := by
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro d _hd
  rw [norm_typeISlabS1_zero]
  by_cases h : d ≤ ⌊U⌋₊
  · rw [if_pos h, if_pos h]
    calc ‖(ArithmeticFunction.moebius d : ℂ)‖ * s1R x d ≤ 1 * s1R x d :=
          mul_le_mul_of_nonneg_right (norm_moebius_intCast_le_one d) (s1R_nonneg x d)
      _ = s1R x d := one_mul _
  · rw [if_neg h, if_neg h]
    simp

private lemma term2_le (x U V : ℝ) :
    (∑ d ∈ theorem51Divisors U V,
        ‖(((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
          ‖typeISlabS0 x 0 d‖)
      ≤ ∑ d ∈ theorem51Divisors U V, Real.log d * s0R x d := by
  apply Finset.sum_le_sum
  intro d _hd
  rw [Complex.norm_real, norm_typeISlabS0_zero]
  exact mul_le_mul_of_nonneg_right (coeff_le_log U V d) (s0R_nonneg x d)

private lemma norm_typeISlabS3_zero_le (x U V : ℝ) :
    ‖typeISlabS3 x 0 U V‖
      ≤ ∑ d ∈ (theorem51Divisors U V).filter (fun d => ⌊U⌋₊ < d), s1R x d := by
  unfold typeISlabS3
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro d _hd
  rw [norm_mul, typeISlabK_zero, Complex.norm_of_nonneg (kR_nonneg x V d)]
  have hmu : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := norm_moebius_intCast_le_one d
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have hkn := kR_nonneg x V d
  have hks := kR_le_s1R x V d
  calc ‖(ArithmeticFunction.moebius d : ℂ) * (1 / 2 : ℂ)‖ * kR x V d
      ≤ 1 * (1 / 2) * kR x V d := by
        rw [norm_mul, h12]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmu (by norm_num)) hkn
    _ ≤ s1R x d := by
        have : 1 * (1 / 2 : ℝ) * kR x V d ≤ 1 * kR x V d :=
          mul_le_mul_of_nonneg_right (by norm_num) hkn
        linarith

lemma theorem51_sharp_transfer_gap_at_zero
    (x U V : ℝ) (_hU : 40 ≤ U) (_hV : 40 ≤ V)
    (_hUx : U < x) (_hVx : V < x)
    (_hUVx : U * V ≤ x / 4) (_hUV2 : x ≤ U * V ^ 2) :
    (∑ d ∈ theorem51Divisors U V,
        (‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖ *
            ‖typeISlabS1 x 0 d‖
          + ‖(((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
              ‖typeISlabS0 x 0 d‖))
      + ‖typeISlabS3 x 0 U V‖
    ≤ ∑ d ∈ theorem51Divisors U V,
        (‖typeISlabS1 x 0 d‖ + Real.log d * ‖typeISlabS0 x 0 d‖) := by
  have h1 := term1_le x U V
  have h2 := term2_le x U V
  have h3 := norm_typeISlabS3_zero_le x U V
  have hsplit : (∑ d ∈ theorem51Divisors U V,
        (‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖ *
            ‖typeISlabS1 x 0 d‖
          + ‖(((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
              ‖typeISlabS0 x 0 d‖))
      = (∑ d ∈ theorem51Divisors U V,
          ‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖ *
            ‖typeISlabS1 x 0 d‖)
        + ∑ d ∈ theorem51Divisors U V,
            ‖(((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
              ‖typeISlabS0 x 0 d‖ := Finset.sum_add_distrib
  have hsplitR : (∑ d ∈ theorem51Divisors U V,
        (‖typeISlabS1 x 0 d‖ + Real.log d * ‖typeISlabS0 x 0 d‖))
      = (∑ d ∈ theorem51Divisors U V, ‖typeISlabS1 x 0 d‖)
        + ∑ d ∈ theorem51Divisors U V, Real.log d * ‖typeISlabS0 x 0 d‖ :=
    Finset.sum_add_distrib
  rw [hsplit, hsplitR]
  have hsplitS1 : (∑ d ∈ (theorem51Divisors U V).filter (fun d => d ≤ ⌊U⌋₊), s1R x d)
      + (∑ d ∈ (theorem51Divisors U V).filter (fun d => ⌊U⌋₊ < d), s1R x d)
      = ∑ d ∈ theorem51Divisors U V, s1R x d := by
    have h := Finset.sum_filter_add_sum_filter_not (theorem51Divisors U V)
        (fun d => d ≤ ⌊U⌋₊) (fun d => s1R x d)
    simpa only [not_le] using h
  have hnormS1 : (∑ d ∈ theorem51Divisors U V, ‖typeISlabS1 x 0 d‖)
      = ∑ d ∈ theorem51Divisors U V, s1R x d :=
    Finset.sum_congr rfl fun d _ => norm_typeISlabS1_zero x d
  have hnormS0 : (∑ d ∈ theorem51Divisors U V, Real.log d * ‖typeISlabS0 x 0 d‖)
      = ∑ d ∈ theorem51Divisors U V, Real.log d * s0R x d :=
    Finset.sum_congr rfl fun d _ => by rw [norm_typeISlabS0_zero]
  rw [hnormS1, hnormS0]
  linarith [h1, h2, h3, hsplitS1]

end TaoFivePrimes

open TaoFivePrimes

theorem solution
    (x U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    (∑ d ∈ theorem51Divisors U V,
        (‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖ *
            ‖typeISlabS1 x 0 d‖
          + ‖(((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
              ‖typeISlabS0 x 0 d‖))
      + ‖typeISlabS3 x 0 U V‖
    ≤ ∑ d ∈ theorem51Divisors U V,
        (‖typeISlabS1 x 0 d‖ + Real.log d * ‖typeISlabS0 x 0 d‖) :=
  TaoFivePrimes.theorem51_sharp_transfer_gap_at_zero x U V hU hV hUx hVx hUVx hUV2

-- Prove2me | solution 1 for TaoFivePrimes.theorem51_typeI_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-12T17:08:21.753925+00:00
-- url     : https://prove2.me/submissions/a4144d51-5149-4860-b501-1c52d5cf290d

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.FiniteSupport.Basic
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_TaoFivePrimes_Theorem51Sums

section

namespace TaoFivePrimes

/-- Exact phase bounds for the positive unit numerator. -/
lemma unit_phase_window (alpha beta q : ℝ) (hq : 0 < q)
    (hphase : 4 * alpha = 1 / q + beta) (hbeta : |beta| ≤ 1 / q ^ 2) :
    (q - 1) / (4 * q ^ 2) ≤ alpha ∧ alpha ≤ (q + 1) / (4 * q ^ 2) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hbeta
  have helo : (q - 1) / (4 * q ^ 2) = (1 / q - 1 / q ^ 2) / 4 := by
    field_simp
    <;> ring
  have hehi : (q + 1) / (4 * q ^ 2) = (1 / q + 1 / q ^ 2) / 4 := by
    field_simp
    <;> ring
  rw [helo, hehi]
  constructor <;> linarith

/-- The reversed sine comparison in the paragraph preceding (5.18)
cannot be used verbatim, even with beta = 0 and q = 1602. This is a
counterexample to that intermediate comparison, not to Theorem 5.1. -/
lemma source_typeI_sine_comparison_fails :
    ¬ (Real.sin (2 * Real.pi * (1 : ℝ) * (1 / (4 * 1602))) ≥
      Real.sin (2 * Real.pi * (1 : ℝ) / (4 * (1602 - 1)))) := by
  have hs : Real.sin (Real.pi / 3204) < Real.sin (Real.pi / 3202) := by
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two <;> linarith [Real.pi_pos]
  have he1 : 2 * Real.pi * (1 : ℝ) * (1 / (4 * 1602)) = Real.pi / 3204 := by ring
  have he2 : 2 * Real.pi * (1 : ℝ) / (4 * (1602 - 1)) = Real.pi / 3202 := by ring
  rw [he1, he2]
  exact not_le_of_gt hs

/-- The numerical parameters in the preceding comparison are in the
actual unit-numerator parameter regime. -/
lemma source_typeI_counterexample_parameters :
    (40 : ℝ) * 40 ≤ 6400 / 4 ∧
    (6400 : ℝ) ≤ 40 * 40 ^ 2 ∧
    (40 : ℝ) * 40 < 1602 - 1 ∧
    (40 : ℝ) < 6400 ∧
    4 * (1 / (4 * 1602) : ℝ) = 1 / 1602 + 0 ∧
    |(0 : ℝ)| ≤ 1 / (1602 : ℝ) ^ 2 := by norm_num

/-- A valid lower sine envelope, keeping the exact lower endpoint of the
phase window instead of substituting its upper endpoint. -/
lemma unit_phase_sine_lower (alpha beta q d : ℝ) (hq : 1 < q)
    (hd : 0 ≤ d) (hdq : d ≤ q - 1)
    (hphase : 4 * alpha = 1 / q + beta) (hbeta : |beta| ≤ 1 / q ^ 2) :
    Real.sin (2 * Real.pi * d * ((q - 1) / (4 * q ^ 2))) ≤
      Real.sin (2 * Real.pi * d * alpha) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hlo, hhi⟩ := unit_phase_window alpha beta q hq0 hphase hbeta
  have hqm : 0 < q - 1 := by linarith
  have ha : 0 ≤ alpha := le_trans (by positivity) hlo
  have hupper : alpha ≤ 1 / (4 * (q - 1)) := by
    apply hhi.trans
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hdalpha : d * alpha ≤ 1 / 4 := by
    calc
      _ ≤ (q - 1) * alpha := mul_le_mul_of_nonneg_right hdq ha
      _ ≤ (q - 1) * (1 / (4 * (q - 1))) :=
        mul_le_mul_of_nonneg_left hupper hqm.le
      _ = 1 / 4 := by field_simp
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  · have hnonneg : 0 ≤ 2 * Real.pi * d * ((q - 1) / (4 * q ^ 2)) := by positivity
    linarith [Real.pi_pos]
  · have hm := mul_le_mul_of_nonneg_left hdalpha (show 0 ≤ 2 * Real.pi by positivity)
    nlinarith
  · exact mul_le_mul_of_nonneg_left hlo (by positivity)

end TaoFivePrimes

end


section

namespace TaoFivePrimes

lemma odd_reciprocal_range_le (q : ℕ) :
    (∑ k ∈ Finset.range (q + 1), 1 / ((2 * k + 1 : ℕ) : ℝ)) ≤
      1 + (1 / 2 : ℝ) * (harmonic q : ℝ) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.mul_zero, Nat.zero_add, Nat.cast_one, div_one]
  have hs : (∑ k ∈ Finset.range q, 1 / ((2 * (k + 1) + 1 : ℕ) : ℝ)) ≤
      (1 / 2 : ℝ) * (harmonic q : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [show (1 / 2 : ℝ) * ((k + 1 : ℕ) : ℝ)⁻¹ =
        1 / (2 * ((k + 1 : ℕ) : ℝ)) by ring]
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    linarith
  linarith

/-- A deliberately loose odd harmonic bound, sufficient for q >= 1602. -/
lemma odd_reciprocal_sum_le (q : ℕ) (s : Finset ℕ)
    (hs : ∀ d ∈ s, d ≤ q ∧ Odd d) :
    (∑ d ∈ s, 1 / (d : ℝ)) ≤ 1.5 + 0.5 * Real.log q := by
  let t := (Finset.range (q + 1)).image (fun k => 2 * k + 1)
  have hsub : s ⊆ t := by
    intro d hd
    obtain ⟨hbound, hodd⟩ := hs d hd
    obtain ⟨k, hk⟩ := hodd.exists_bit1
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_range.mpr (by omega), hk.symm⟩
  have he : (∑ d ∈ t, 1 / (d : ℝ)) =
      ∑ k ∈ Finset.range (q + 1), 1 / ((2 * k + 1 : ℕ) : ℝ) := by
    dsimp [t]
    rw [Finset.sum_image]
    intro a ha b hb hab
    change 2 * a + 1 = 2 * b + 1 at hab
    omega
  have hle : (∑ d ∈ s, 1 / (d : ℝ)) ≤ ∑ d ∈ t, 1 / (d : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  rw [he] at hle
  have hH := harmonic_le_one_add_log q
  have hr := odd_reciprocal_range_le q
  linarith

lemma sum_indices_le_square (q : ℕ) (s : Finset ℕ)
    (hs : ∀ d ∈ s, d < q) :
    (∑ d ∈ s, (d : ℝ)) ≤ (q : ℝ) ^ 2 := by
  have hsub : s ⊆ Finset.range q := fun d hd => Finset.mem_range.mpr (hs d hd)
  have hc : s.card ≤ q := by simpa using Finset.card_le_card hsub
  calc
    _ ≤ ∑ _d ∈ s, (q : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact_mod_cast (hs d hd).le
    _ = (s.card : ℝ) * q := by simp
    _ ≤ (q : ℝ) * q := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _)
    _ = _ := by ring

end TaoFivePrimes

end


section

namespace TaoFivePrimes

/-- A global quadratic cosecant envelope on the positive half-quadrant. -/
lemma sine_quadratic_envelope (t : ℝ) (ht : 0 < t) (htpi : t ≤ Real.pi / 2) :
    t ^ 2 ≤ (1 + t ^ 2) * Real.sin t ^ 2 := by
  have htB : t ≤ (5 / 3 : ℝ) := by linarith [Real.pi_lt_d2]
  have ht3 : t ^ 2 ≤ 3 := by
    have hb := (sq_le_sq₀ ht.le (by norm_num : (0 : ℝ) ≤ 5 / 3)).2 htB
    norm_num at hb
    linarith
  let r : ℝ := 1 - t ^ 2 / 6
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hs : t * r ≤ Real.sin t := by
    have h := Real.sin_ge_sub_cube ht.le
    dsimp [r]
    nlinarith
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  have hR : 1 ≤ (1 + t ^ 2) * r ^ 2 := by
    apply sub_nonneg.mp
    have he : (1 + t ^ 2) * r ^ 2 - 1 = t ^ 2 * (3 - t ^ 2) * (8 - t ^ 2) / 36 := by
      dsimp [r]
      ring
    rw [he]
    have h3 : 0 ≤ 3 - t ^ 2 := by linarith
    have h8 : 0 ≤ 8 - t ^ 2 := by linarith
    positivity
  calc
    t ^ 2 ≤ t ^ 2 * ((1 + t ^ 2) * r ^ 2) := by nlinarith [sq_nonneg t]
    _ = (1 + t ^ 2) * (t * r) ^ 2 := by ring
    _ ≤ (1 + t ^ 2) * Real.sin t ^ 2 :=
      mul_le_mul_of_nonneg_left ((sq_le_sq₀ (mul_nonneg ht.le hr) hsin.le).2 hs) (by positivity)

lemma cosecant_sq_le_inv_sq_add_one (t : ℝ) (ht : 0 < t) (htpi : t ≤ Real.pi / 2) :
    1 / Real.sin t ^ 2 ≤ 1 / t ^ 2 + 1 := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  have h := sine_quadratic_envelope t ht htpi
  apply (div_le_iff₀ (sq_pos_of_pos hs)).2
  rw [show (1 / t ^ 2 + 1) * Real.sin t ^ 2 =
    ((1 + t ^ 2) * Real.sin t ^ 2) / t ^ 2 by field_simp]
  apply (le_div_iff₀ (sq_pos_of_pos ht)).2
  nlinarith

/-- Transfer the quadratic sine envelope to a weighted reciprocal. -/
lemma weighted_cosecant_envelope (d q t y : ℝ) (hd : 0 < d) (ht : 0 < t)
    (htpi : t ≤ Real.pi / 2) (hy : Real.sin t ≤ y)
    (hscale : d ^ 2 ≤ 0.41 * q ^ 2 * t ^ 2) :
    d / y ^ 2 ≤ 0.41 * q ^ 2 / d + d := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  calc
    _ ≤ d / Real.sin t ^ 2 := div_le_div_of_nonneg_left hd.le
      (sq_pos_of_pos hs) ((sq_le_sq₀ hs.le (hs.le.trans hy)).2 hy)
    _ = d * (1 / Real.sin t ^ 2) := by ring
    _ ≤ d * (1 / t ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left (cosecant_sq_le_inv_sq_add_one t ht htpi) hd.le
    _ = d / t ^ 2 + d := by ring
    _ ≤ _ := by
      suffices h : d / t ^ 2 ≤ 0.41 * q ^ 2 / d by linarith
      apply (div_le_div_iff₀ (sq_pos_of_pos ht) hd).2
      nlinarith

/-- A pointwise bound using the corrected phase endpoint, with numerical
slack that will be recovered by retaining odd summation indices. -/
lemma unit_cosecant_pointwise (alpha beta q d : ℝ) (hq : 1602 ≤ q)
    (hd : 0 < d) (hdq : d ≤ q - 1)
    (hphase : 4 * alpha = 1 / q + beta) (hbeta : |beta| ≤ 1 / q ^ 2) :
    d / Real.sin (2 * Real.pi * d * alpha) ^ 2 ≤ 0.41 * q ^ 2 / d + d := by
  have hq0 : 0 < q := by linarith
  have hqm : 0 < q - 1 := by linarith
  let t : ℝ := Real.pi * d * (q - 1) / (2 * q ^ 2)
  have ht : 0 < t := by dsimp [t]; positivity
  have hdqm : d * (q - 1) ≤ q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hdq hqm.le
    nlinarith
  have htpi : t ≤ Real.pi / 2 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hdqm Real.pi_pos.le]
  have hbase : (25 / 8 : ℝ) * q ≤ Real.pi * (q - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_gt_d2.le) hqm.le]
  have hscaled : (25 / 16 : ℝ) * d ≤ t * q := by
    have he : t * q = Real.pi * d * (q - 1) / (2 * q) := by
      dsimp [t]
      field_simp
    rw [he]
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_right hbase hd.le]
  have hscale : d ^ 2 ≤ 0.41 * q ^ 2 * t ^ 2 := by
    have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (25 / 16 : ℝ) * d)
      (by positivity : 0 ≤ t * q)).2 hscaled
    nlinarith [sq_nonneg d]
  have hsin : Real.sin t ≤ Real.sin (2 * Real.pi * d * alpha) := by
    convert unit_phase_sine_lower alpha beta q d (by linarith) hd.le hdq hphase hbeta using 1
    congr 1
    dsimp [t]
    ring
  exact weighted_cosecant_envelope d q t _ hd ht htpi hsin hscale

lemma log_denominator_lower (q : ℕ) (hq : 1602 ≤ q) : (6.5 : ℝ) ≤ Real.log q := by
  have hqR : (1024 : ℝ) ≤ q := by exact_mod_cast (show 1024 ≤ q by omega)
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1024) hqR
  have he : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  rw [he] at h
  linarith [Real.log_two_gt_d9]

lemma typeI_numeric_slack (q : ℕ) (hq : 1602 ≤ q) :
    (q : ℝ) ^ 2 * (0.41 * (1.5 + 0.5 * Real.log q) + 1) ≤
      (4 / Real.pi ^ 2) * (q : ℝ) ^ 2 * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlog := log_denominator_lower q hq
  have hpi : Real.pi ^ 2 ≤ 10 := by
    have h := (sq_le_sq₀ Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 3.15)).2 Real.pi_lt_d2.le
    norm_num at h
    linarith
  have hc : (0.4 : ℝ) ≤ 4 / Real.pi ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).2
    nlinarith
  have harg : Real.exp 1 * q ≤ 4 * Real.exp 1 * q / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith [mul_le_mul_of_nonneg_left Real.pi_lt_four.le
      (show 0 ≤ Real.exp 1 * q by positivity)]
  have hl := Real.log_le_log (show 0 < Real.exp 1 * q by positivity) harg
  rw [Real.log_mul (Real.exp_ne_zero _) hq0.ne', Real.log_exp] at hl
  have hL : 0 ≤ 1 + Real.log q := by linarith
  calc
    _ ≤ (q : ℝ) ^ 2 * (0.4 * (1 + Real.log q)) := by gcongr; linarith
    _ = 0.4 * (q : ℝ) ^ 2 * (1 + Real.log q) := by ring
    _ ≤ _ := by gcongr

/-- The complete odd-index trigonometric sum bound with the constant needed
for (5.7), using the corrected lower phase endpoint. -/
theorem unit_typeI_trigonometric_sum (alpha beta : ℝ) (q : ℕ) (s : Finset ℕ)
    (hq : 1602 ≤ q)
    (hs : ∀ d ∈ s, 0 < d ∧ (d : ℝ) ≤ (q : ℝ) - 1 ∧ Odd d)
    (hphase : 4 * alpha = 1 / (q : ℝ) + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ d ∈ s, (d : ℝ) / Real.sin (2 * Real.pi * d * alpha) ^ 2) ≤
      (4 / Real.pi ^ 2) * (q : ℝ) ^ 2 * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  have hslt : ∀ d ∈ s, d < q := by
    intro d hd
    have hb := (hs d hd).2.1
    exact_mod_cast (show (d : ℝ) < q by linarith)
  have hrec := odd_reciprocal_sum_le q s (fun d hd => ⟨(hslt d hd).le, (hs d hd).2.2⟩)
  have hsum := sum_indices_le_square q s hslt
  calc
    _ ≤ ∑ d ∈ s, (0.41 * (q : ℝ) ^ 2 / (d : ℝ) + d) := by
      apply Finset.sum_le_sum
      intro d hd
      exact unit_cosecant_pointwise alpha beta q d (by exact_mod_cast hq)
        (by exact_mod_cast (hs d hd).1) (hs d hd).2.1 hphase hbeta
    _ = 0.41 * (q : ℝ) ^ 2 * (∑ d ∈ s, 1 / (d : ℝ)) + ∑ d ∈ s, (d : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ 0.41 * (q : ℝ) ^ 2 * (1.5 + 0.5 * Real.log q) + (q : ℝ) ^ 2 := by gcongr
    _ = (q : ℝ) ^ 2 * (0.41 * (1.5 + 0.5 * Real.log q) + 1) := by ring
    _ ≤ _ := typeI_numeric_slack q hq

/-- Both signs of the unit numerator give the same squared sine sum. -/
theorem unit_typeI_trigonometric_sum_signed (alpha beta : ℝ) (a : ℤ)
    (q : ℕ) (s : Finset ℕ) (hq : 1602 ≤ q) (ha : a.natAbs = 1)
    (hs : ∀ d ∈ s, 0 < d ∧ (d : ℝ) ≤ (q : ℝ) - 1 ∧ Odd d)
    (hphase : 4 * alpha = (a : ℝ) / (q : ℝ) + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ d ∈ s, (d : ℝ) / Real.sin (2 * Real.pi * d * alpha) ^ 2) ≤
      (4 / Real.pi ^ 2) * (q : ℝ) ^ 2 * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  rcases Int.natAbs_eq_iff.mp ha with ha | ha
  · norm_num at ha
    subst a
    exact unit_typeI_trigonometric_sum alpha beta q s hq hs (by simpa using hphase) hbeta
  · norm_num at ha
    subst a
    have hp : 4 * (-alpha) = 1 / (q : ℝ) + (-beta) := by
      norm_num at hphase
      rw [neg_div] at hphase
      linarith
    have h := unit_typeI_trigonometric_sum (-alpha) (-beta) q s hq hs hp (by simpa using hbeta)
    simpa only [mul_neg, Real.sin_neg, neg_sq] using h

lemma unit_regime_denominator_large (U V : ℝ) (q : ℕ)
    (hU : 40 ≤ U) (hV : 40 ≤ V) (hUVq : U * V < (q : ℝ) - 1) : 1602 ≤ q := by
  have h : (1601 : ℝ) < q := by
    nlinarith [mul_nonneg (show 0 ≤ U - 40 by linarith) (show 0 ≤ V - 40 by linarith)]
  have hn : 1601 < q := by exact_mod_cast h
  omega

/-- The full Type I outer-sum assembly. Its pointwise decay hypothesis is
the remaining smoothing obligation and is stated explicitly. -/
theorem unit_typeI_of_pointwise_decay (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ)
    (s : Finset ℕ) (T : ℕ → ℂ)
    (hx : 1 ≤ x) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUVq : U * V < (q : ℝ) - 1) (ha : a.natAbs = 1)
    (hs : ∀ d ∈ s, 0 < d ∧ (d : ℝ) ≤ U * V ∧ d.Coprime 2)
    (hphase : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hdecay : ∀ d ∈ s, ‖T d‖ ≤ (24 * Real.log (4 * x) / x) *
      ((d : ℝ) / Real.sin (2 * Real.pi * d * alpha) ^ 2)) :
    (∑ d ∈ s, ‖T d‖) ≤ (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
      Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  have hq := unit_regime_denominator_large U V q hU hV hUVq
  have hx0 : 0 < x := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlog : 0 ≤ Real.log (4 * x) := Real.log_nonneg (by linarith)
  have hK : 0 ≤ 24 * Real.log (4 * x) / x := by positivity
  have htrig := unit_typeI_trigonometric_sum_signed alpha beta a q s hq ha
    (fun d hd => ⟨(hs d hd).1, (hs d hd).2.1.trans hUVq.le,
      Nat.coprime_two_right.mp (hs d hd).2.2⟩) hphase hbeta
  calc
    _ ≤ ∑ d ∈ s, (24 * Real.log (4 * x) / x) *
        ((d : ℝ) / Real.sin (2 * Real.pi * d * alpha) ^ 2) :=
      Finset.sum_le_sum hdecay
    _ = (24 * Real.log (4 * x) / x) *
        (∑ d ∈ s, (d : ℝ) / Real.sin (2 * Real.pi * d * alpha) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (24 * Real.log (4 * x) / x) *
        ((4 / Real.pi ^ 2) * (q : ℝ) ^ 2 * Real.log (4 * Real.exp 1 * q / Real.pi)) :=
      mul_le_mul_of_nonneg_left htrig hK
    _ = _ := by field_simp; ring

end TaoFivePrimes

end


section

namespace TaoFivePrimes

noncomputable def twistedSecondDifference (z : ℂ) (f : ℤ → ℂ) (n : ℤ) : ℂ :=
  f (n + 2) - 2 * z * f (n + 1) + z ^ 2 * f n

/-- Discrete summation by parts twice, without differentiability assumptions. -/
lemma tsum_twistedSecondDifference (z : ℂ) (f : ℤ → ℂ) (hf : Summable f) :
    (∑' n : ℤ, twistedSecondDifference z f n) = (1 - z) ^ 2 * ∑' n : ℤ, f n := by
  have hf1 : Summable (fun n : ℤ => f (n + 1)) :=
    hf.comp_injective (by intro a b h; change a + 1 = b + 1 at h; omega)
  have hf2 : Summable (fun n : ℤ => f (n + 2)) :=
    hf.comp_injective (by intro a b h; change a + 2 = b + 2 at h; omega)
  have he1 : (∑' n : ℤ, f (n + 1)) = ∑' n : ℤ, f n := (Equiv.addRight 1).tsum_eq f
  have he2 : (∑' n : ℤ, f (n + 2)) = ∑' n : ℤ, f n := (Equiv.addRight 2).tsum_eq f
  simp only [twistedSecondDifference]
  rw [Summable.tsum_add (hf2.sub (hf1.mul_left (2 * z))) (hf.mul_left (z ^ 2)),
    Summable.tsum_sub hf2 (hf1.mul_left (2 * z)), tsum_mul_left, tsum_mul_left, he1, he2]
  ring

/-- The reciprocal-square denominator in the Type I estimate follows from
an l1 bound on discrete second differences. -/
lemma norm_tsum_le_twistedSecondDifference (z : ℂ) (f : ℤ → ℂ)
    (hz : z ≠ 1) (hf : Summable f)
    (hD : Summable (fun n : ℤ => ‖twistedSecondDifference z f n‖)) :
    ‖∑' n : ℤ, f n‖ ≤ (∑' n : ℤ, ‖twistedSecondDifference z f n‖) / ‖1 - z‖ ^ 2 := by
  have h := norm_tsum_le_tsum_norm hD
  rw [tsum_twistedSecondDifference z f hf, norm_mul, norm_pow] at h
  have hp : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz))
  apply (le_div_iff₀ (sq_pos_of_pos hp)).2
  nlinarith

lemma norm_exp_gap_sq (theta : ℝ) :
    ‖(1 : ℂ) - Complex.exp (Complex.I * theta)‖ ^ 2 = 4 * Real.sin (theta / 2) ^ 2 := by
  rw [norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, sq_abs]
  ring

lemma norm_tsum_le_sine_second_difference (theta : ℝ) (f : ℤ → ℂ)
    (hs : Real.sin (theta / 2) ≠ 0) (hf : Summable f)
    (hD : Summable (fun n : ℤ => ‖twistedSecondDifference (Complex.exp (Complex.I * theta)) f n‖)) :
    ‖∑' n : ℤ, f n‖ ≤
      (∑' n : ℤ, ‖twistedSecondDifference (Complex.exp (Complex.I * theta)) f n‖) /
        (4 * Real.sin (theta / 2) ^ 2) := by
  have hz : Complex.exp (Complex.I * theta) ≠ 1 := by
    intro h
    have he := norm_exp_gap_sq theta
    rw [h, sub_self, norm_zero] at he
    have hp := sq_pos_of_ne_zero hs
    nlinarith
  have h := norm_tsum_le_twistedSecondDifference _ f hz hf hD
  rwa [norm_exp_gap_sq] at h

/-- Twisted differences remove the geometric phase exactly. -/
lemma twistedSecondDifference_geometric (z : ℂ) (hz : z ≠ 0) (F : ℤ → ℂ) (n : ℤ) :
    twistedSecondDifference z (fun k => F k * z ^ k) n =
      z ^ (n + 2) * (F (n + 2) - 2 * F (n + 1) + F n) := by
  simp only [twistedSecondDifference, zpow_add₀ hz, zpow_ofNat, zpow_one]
  ring

/-- A finite Fourier sum is controlled by the total discrete second
variation of its amplitude. In particular, amplitude corners are allowed. -/
theorem finite_fourier_second_difference_bound (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    (F : ℤ → ℂ) (hF : Function.HasFiniteSupport F) :
    ‖∑' n : ℤ, F n * z ^ n‖ ≤
      (∑' n : ℤ, ‖F (n + 2) - 2 * F (n + 1) + F n‖) / ‖1 - z‖ ^ 2 := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hF1 : Function.HasFiniteSupport (fun n : ℤ => F (n + 1)) :=
    hF.fun_comp_of_injective (by intro a b h; change a + 1 = b + 1 at h; omega)
  have hF2 : Function.HasFiniteSupport (fun n : ℤ => F (n + 2)) :=
    hF.fun_comp_of_injective (by intro a b h; change a + 2 = b + 2 at h; omega)
  have hDelta : Function.HasFiniteSupport (fun n : ℤ => F (n + 2) - 2 * F (n + 1) + F n) :=
    (hF2.sub (hF1.fun_comp (show (2 : ℂ) * 0 = 0 by simp))).add hF
  have hG : Summable (fun n : ℤ => F n * z ^ n) :=
    summable_of_hasFiniteSupport (hF.mul_left (fun n => z ^ n))
  have he (n : ℤ) : ‖twistedSecondDifference z (fun k => F k * z ^ k) n‖ =
      ‖F (n + 2) - 2 * F (n + 1) + F n‖ := by
    rw [twistedSecondDifference_geometric z hz0, norm_mul, norm_zpow, hz, one_zpow, one_mul]
  have hD : Summable (fun n : ℤ => ‖twistedSecondDifference z (fun k => F k * z ^ k) n‖) :=
    (summable_of_hasFiniteSupport (hDelta.fun_comp norm_zero)).congr (fun n => (he n).symm)
  have h := norm_tsum_le_twistedSecondDifference z _ hz1 hG hD
  simpa only [he] using h

end TaoFivePrimes

end


section

namespace TaoFivePrimes

lemma positive_unit_sine_pos (alpha beta q d : ℝ) (hq : 1 < q)
    (hd : 0 < d) (hdq : d ≤ q - 1)
    (hphase : 4 * alpha = 1 / q + beta) (hbeta : |beta| ≤ 1 / q ^ 2) :
    0 < Real.sin (2 * Real.pi * d * alpha) := by
  have hq0 : 0 < q := by linarith
  have hqm : 0 < q - 1 := by linarith
  let t : ℝ := 2 * Real.pi * d * ((q - 1) / (4 * q ^ 2))
  have ht : 0 < t := by dsimp [t]; positivity
  have he : t = Real.pi * (d * (q - 1)) / (2 * q ^ 2) := by dsimp [t]; ring
  have hb : d * (q - 1) ≤ q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hdq hqm.le
    nlinarith
  have htpi : t ≤ Real.pi / 2 := by
    rw [he]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hb Real.pi_pos.le]
  have hp : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  exact hp.trans_le (unit_phase_sine_lower alpha beta q d hq hd.le hdq hphase hbeta)

lemma unit_sine_ne_zero (alpha beta : ℝ) (a : ℤ) (q : ℕ) (d : ℝ)
    (hq : 1602 ≤ q) (ha : a.natAbs = 1) (hd : 0 < d) (hdq : d ≤ (q : ℝ) - 1)
    (hphase : 4 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    Real.sin (2 * Real.pi * d * alpha) ≠ 0 := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  rcases Int.natAbs_eq_iff.mp ha with ha | ha
  · norm_num at ha
    subst a
    exact (positive_unit_sine_pos alpha beta q d hqR hd hdq (by simpa using hphase) hbeta).ne'
  · norm_num at ha
    subst a
    have hp : 4 * (-alpha) = 1 / (q : ℝ) + (-beta) := by
      norm_num at hphase
      rw [neg_div] at hphase
      linarith
    have h := (positive_unit_sine_pos (-alpha) (-beta) q d hqR hd hdq hp (by simpa using hbeta)).ne'
    simpa only [mul_neg, Real.sin_neg, neg_ne_zero] using h

/-- The Type I bound from a concrete discrete-variation hypothesis.
The unresolved smoothing input is the displayed bound on the amplitude's
second differences; all Fourier cancellation and outer summation are proved. -/
theorem unit_typeI_from_discrete_variation
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ) (s : Finset ℕ) (F : ℕ → ℤ → ℂ)
    (hx : 1 ≤ x) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUVq : U * V < (q : ℝ) - 1) (ha : a.natAbs = 1)
    (hs : ∀ d ∈ s, 0 < d ∧ (d : ℝ) ≤ U * V ∧ d.Coprime 2)
    (hphase : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hfinite : ∀ d ∈ s, Function.HasFiniteSupport (F d))
    (hvariation : ∀ d ∈ s,
      (∑' n : ℤ, ‖F d (n + 2) - 2 * F d (n + 1) + F d n‖) ≤
        96 * Real.log (4 * x) / x * d) :
    (∑ d ∈ s, ‖∑' n : ℤ, F d n *
      (Complex.exp (Complex.I * ((4 * Real.pi * (d : ℝ) * alpha : ℝ) : ℂ))) ^ n‖) ≤
      (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
        Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  apply unit_typeI_of_pointwise_decay x alpha beta U V a q s _ hx hU hV hUVq ha hs hphase hbeta
  intro d hd
  have hq := unit_regime_denominator_large U V q hU hV hUVq
  have hsin := unit_sine_ne_zero alpha beta a q d hq ha (by exact_mod_cast (hs d hd).1)
    ((hs d hd).2.1.trans hUVq.le) hphase hbeta
  let theta : ℝ := 4 * Real.pi * d * alpha
  let z : ℂ := Complex.exp (Complex.I * theta)
  have hz : ‖z‖ = 1 := Complex.norm_exp_I_mul_ofReal theta
  have htheta : theta / 2 = 2 * Real.pi * d * alpha := by dsimp [theta]; ring
  have hgap : ‖1 - z‖ ^ 2 = 4 * Real.sin (2 * Real.pi * d * alpha) ^ 2 := by
    rw [show z = Complex.exp (Complex.I * theta) from rfl, norm_exp_gap_sq, htheta]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero, zero_pow (by decide)] at hgap
    nlinarith [sq_pos_of_ne_zero hsin]
  have h := finite_fourier_second_difference_bound z hz hz1 (F d) (hfinite d hd)
  change ‖∑' n : ℤ, F d n * z ^ n‖ ≤ _
  rw [hgap] at h
  calc
    _ ≤ (∑' n : ℤ, ‖F d (n + 2) - 2 * F d (n + 1) + F d n‖) /
        (4 * Real.sin (2 * Real.pi * d * alpha) ^ 2) := h
    _ ≤ (96 * Real.log (4 * x) / x * d) /
        (4 * Real.sin (2 * Real.pi * d * alpha) ^ 2) := by
      apply div_le_div_of_nonneg_right (hvariation d hd)
      positivity
    _ = _ := by ring

end TaoFivePrimes

end


section

namespace TaoFivePrimes

lemma eta0_zero_below_quarter {t : ℝ} (ht : t ≤ 1 / 4) : eta0 t = 0 := by
  unfold eta0
  split_ifs with hp
  · have hlog : Real.log (2 * t) ≤ -Real.log 2 := by
      have h := Real.log_le_log (show 0 < 2 * t by positivity)
        (show 2 * t ≤ (1 / 2 : ℝ) by linarith)
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv] at h
      exact h
    have hab : Real.log 2 ≤ |Real.log (2 * t)| := by
      linarith [neg_le_abs (Real.log (2 * t))]
    rw [max_eq_left (by linarith), mul_zero]
  · rfl

lemma eta0_zero_above_one {t : ℝ} (ht : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  rw [if_pos (by linarith)]
  have hl : Real.log 2 ≤ Real.log (2 * t) := Real.log_le_log (by norm_num) (by linarith)
  have hm : Real.log 2 - |Real.log (2 * t)| ≤ 0 := by
    linarith [le_abs_self (Real.log (2 * t))]
  rw [max_eq_left hm, mul_zero]

lemma eta0_lower_piece {t : ℝ} (hlo : 1 / 4 ≤ t) (hhi : t ≤ 1 / 2) :
    eta0 t = 4 * Real.log (4 * t) := by
  have ht : 0 < t := by linarith
  have hneg : Real.log (2 * t) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  have he : Real.log 2 + Real.log (2 * t) = Real.log (4 * t) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
    congr 1
    ring
  unfold eta0
  rw [if_pos ht, abs_of_nonpos hneg, sub_neg_eq_add, he,
    max_eq_right (Real.log_nonneg (by linarith))]

lemma eta0_upper_piece {t : ℝ} (hlo : 1 / 2 ≤ t) (hhi : t ≤ 1) :
    eta0 t = -4 * Real.log t := by
  have ht : 0 < t := by linarith
  have hpos : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith)
  have he : Real.log 2 - Real.log (2 * t) = -Real.log t := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht.ne']
    ring
  unfold eta0
  rw [if_pos ht, abs_of_nonneg hpos, he,
    max_eq_right (neg_nonneg.mpr (Real.log_nonpos ht.le hhi))]
  ring

/-- Actual odd-lattice amplitude in a Type I inner sum. -/
noncomputable def typeIOddAmplitude (x d : ℝ) (c : ℂ) (n : ℤ) : ℂ :=
  ((Real.log ((2 * n + 1 : ℤ) : ℝ) : ℂ) + c * (Real.log d : ℂ)) *
    (eta0 (d * ((2 * n + 1 : ℤ) : ℝ) / x) : ℂ)

lemma typeIOddAmplitude_finite (x d : ℝ) (c : ℂ) (hx : 0 < x) (hd : 0 < d) :
    Function.HasFiniteSupport (typeIOddAmplitude x d c) := by
  apply (Set.finite_Icc (0 : ℤ) ⌈x / d⌉).subset
  intro n hn
  by_contra hnot
  have hz : typeIOddAmplitude x d c n = 0 := by
    unfold typeIOddAmplitude
    suffices he : eta0 (d * ((2 * n + 1 : ℤ) : ℝ) / x) = 0 by rw [he]; simp
    simp only [Set.mem_Icc, not_and_or, not_le] at hnot
    rcases hnot with hlo | hhi
    · apply eta0_zero_below_quarter
      have hn0 : n ≤ -1 := by omega
      have hy : ((2 * n + 1 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast (show 2 * n + 1 ≤ 0 by omega)
      have hh : d * ((2 * n + 1 : ℤ) : ℝ) / x ≤ 0 := div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hd.le hy) hx.le
      linarith
    · apply eta0_zero_above_one
      have hceil : x / d ≤ (⌈x / d⌉ : ℤ) := Int.le_ceil _
      have hnR : ((⌈x / d⌉ : ℤ) : ℝ) < n := by exact_mod_cast hhi
      have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (div_pos hx hd) (hceil.trans hnR.le)
      have hy : x / d ≤ ((2 * n + 1 : ℤ) : ℝ) := by push_cast; linarith
      apply (le_div_iff₀ hx).2
      have hh := (div_le_iff₀ hd).mp hy
      nlinarith
  exact hn hz

end TaoFivePrimes

end


section

namespace TaoFivePrimes

lemma expCircle_odd_geometric (alpha d : ℝ) (n : ℤ) :
    expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ)) =
      expCircle (alpha * d) *
        (Complex.exp (Complex.I * ((4 * Real.pi * d * alpha : ℝ) : ℂ))) ^ n := by
  unfold expCircle
  rw [← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma expCircle_norm_unit (t : ℝ) : ‖expCircle t‖ = 1 := by
  unfold expCircle
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
    Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) by push_cast; ring]
  exact Complex.norm_exp_I_mul_ofReal _

/-- Removing the harmless unit phase is exact, for every integer-indexed amplitude. -/
lemma norm_odd_fourier_eq_geometric (alpha d : ℝ) (F : ℤ → ℂ) :
    ‖∑' n : ℤ, F n * expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ))‖ =
      ‖∑' n : ℤ, F n *
        (Complex.exp (Complex.I * ((4 * Real.pi * d * alpha : ℝ) : ℂ))) ^ n‖ := by
  simp_rw [expCircle_odd_geometric, mul_left_comm (F _) (expCircle (alpha * d))]
  rw [tsum_mul_left, norm_mul, expCircle_norm_unit, one_mul]

/-- Actual odd-lattice Type I sum: no smoothness hypothesis is used. -/
theorem typeI_odd_sum_second_difference_bound (x d alpha : ℝ) (c : ℂ)
    (hx : 0 < x) (hd : 0 < d) (hsin : Real.sin (2 * Real.pi * d * alpha) ≠ 0) :
    ‖∑' n : ℤ, typeIOddAmplitude x d c n *
      expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ))‖ ≤
    (∑' n : ℤ, ‖typeIOddAmplitude x d c (n + 2) -
      2 * typeIOddAmplitude x d c (n + 1) + typeIOddAmplitude x d c n‖) /
      (4 * Real.sin (2 * Real.pi * d * alpha) ^ 2) := by
  rw [norm_odd_fourier_eq_geometric]
  let theta : ℝ := 4 * Real.pi * d * alpha
  let z : ℂ := Complex.exp (Complex.I * (theta : ℂ))
  have hz : ‖z‖ = 1 := Complex.norm_exp_I_mul_ofReal theta
  have hgap : ‖1 - z‖ ^ 2 = 4 * Real.sin (2 * Real.pi * d * alpha) ^ 2 := by
    dsimp [z]
    rw [norm_exp_gap_sq, show theta / 2 = 2 * Real.pi * d * alpha by dsimp [theta]; ring]
  have hz1 : z ≠ 1 := by
    intro he
    rw [he, sub_self, norm_zero, zero_pow (by decide)] at hgap
    nlinarith [sq_pos_of_ne_zero hsin]
  have h := finite_fourier_second_difference_bound z hz hz1
    (typeIOddAmplitude x d c) (typeIOddAmplitude_finite x d c hx hd)
  rw [hgap] at h
  exact h

end TaoFivePrimes

end


section

namespace TaoFivePrimes

/-- The logarithmic coefficient never exceeds log x on the cutoff support. -/
lemma typeI_log_coefficient_bound (x d y : ℝ) (c : ℂ)
    (hd : 1 ≤ d) (hy : 1 ≤ y) (hxy : d * y ≤ x) (hc : ‖c‖ ≤ 1) :
    ‖(Real.log y : ℂ) + c * (Real.log d : ℂ)‖ ≤ Real.log x := by
  have hd0 : 0 < d := by linarith
  have hy0 : 0 < y := by linarith
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy
  calc
    _ ≤ ‖(Real.log y : ℂ)‖ + ‖c * (Real.log d : ℂ)‖ := norm_add_le _ _
    _ = Real.log y + ‖c‖ * Real.log d := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hly, abs_of_nonneg hld]
    _ ≤ Real.log y + Real.log d := by nlinarith
    _ = Real.log (d * y) := by rw [Real.log_mul hd0.ne' hy0.ne']; ring
    _ ≤ Real.log x := Real.log_le_log (mul_pos hd0 hy0) hxy

/-- Each smooth piece of the logarithmic amplitude has this universal form. -/
lemma log_product_hasDerivAt (y : ℝ) (hy : y ≠ 0) (b k : ℂ) :
    HasDerivAt (fun t : ℝ => 4 * ((Real.log t : ℂ) + k) * ((Real.log t : ℂ) + b))
      (4 / (y : ℂ) * (2 * (Real.log y : ℂ) + b + k)) y := by
  have h := (((Real.hasDerivAt_log hy).ofReal_comp.add_const k).const_mul 4).mul
    ((Real.hasDerivAt_log hy).ofReal_comp.add_const b)
  convert h using 1 <;> first | rfl | (simp only [Complex.ofReal_inv, div_eq_mul_inv]; ring)

lemma log_product_derivative_hasDerivAt (y : ℝ) (hy : y ≠ 0) (b k : ℂ) :
    HasDerivAt (fun t : ℝ => 4 / (t : ℂ) * (2 * (Real.log t : ℂ) + b + k))
      (4 / (y : ℂ) ^ 2 * (2 - 2 * (Real.log y : ℂ) - b - k)) y := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have h := ((hasDerivAt_const y (4 : ℂ)).div
    (hasDerivAt_id y).ofReal_comp hyC).mul
      ((((Real.hasDerivAt_log hy).ofReal_comp.const_mul 2).add_const b).add_const k)
  convert h using 1 <;> first | rfl | (simp only [Pi.div_apply, id_eq,
    Complex.ofReal_one, Complex.ofReal_inv]; field_simp; ring)

/-- A uniform majorant for the curvature of either logarithmic piece.
Here L is the logarithm in the cutoff and g is the logarithmic coefficient. -/
lemma typeI_curvature_majorant (y X L : ℝ) (g : ℂ) (hy : 0 < y)
    (hg : ‖g‖ ≤ X) (hL : |L| ≤ 3 / 4) :
    ‖(4 / (y : ℂ) ^ 2) * (2 - g - (L : ℂ))‖ ≤ (4 * X + 11) / y ^ 2 := by
  have hb : ‖(2 : ℂ) - g - (L : ℂ)‖ ≤ 2 + X + 3 / 4 := by
    calc
      _ ≤ ‖(2 : ℂ) - g‖ + ‖(L : ℂ)‖ := norm_sub_le _ _
      _ ≤ (‖(2 : ℂ)‖ + ‖g‖) + ‖(L : ℂ)‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ 2 + X + 3 / 4 := by
        norm_num [Complex.norm_real, Real.norm_eq_abs]
        linarith
  have he : ‖(4 : ℂ) / (y : ℂ) ^ 2‖ = 4 / y ^ 2 := by
    simp [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  rw [norm_mul, he]
  calc
    _ ≤ (4 / y ^ 2) * (2 + X + 3 / 4) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- Exact integral of the regular-curvature majorant over the cutoff support. -/
lemma typeI_curvature_majorant_integral (r X : ℝ) (hr : 0 < r) :
    (∫ y in r / 4..r, (4 * X + 11) / y ^ 2) = (12 * X + 33) / r := by
  have hz : (0 : ℝ) ∉ Set.uIcc (r / 4) r := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  have hi := integral_zpow (a := r / 4) (b := r) (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, hz⟩)
  norm_num at hi
  have he (y : ℝ) : (4 * X + 11) / y ^ 2 = (4 * X + 11) * y ^ (-2 : ℤ) := by
    simp [zpow_neg, div_eq_mul_inv]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  simp only [zpow_neg, zpow_ofNat]
  rw [hi]
  field_simp
  ring

/-- The three slope jumps contribute at most 36 log(x)/r.
Together with the regular-curvature integral there is room in 48 log(4x)/r.
The passage from this budget to discrete variation is a separate obligation. -/
lemma typeI_curvature_and_jump_budget (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    (12 * Real.log x + 33) / r + 36 * Real.log x / r ≤
      48 * Real.log (4 * x) / r := by
  have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hx.ne', hl4]
  apply (le_div_iff₀ hr).2
  field_simp
  nlinarith [Real.log_two_gt_d9]

lemma typeI_amplitude_lower_formula (r d y : ℝ) (c : ℂ)
    (hr : 0 < r) (hy : 0 < y) (hlo : 1 / 4 ≤ y / r) (hhi : y / r ≤ 1 / 2) :
    ((Real.log y : ℂ) + c * (Real.log d : ℂ)) * (eta0 (y / r) : ℂ) =
      4 * ((Real.log y : ℂ) + (Real.log (4 / r) : ℂ)) *
        ((Real.log y : ℂ) + c * (Real.log d : ℂ)) := by
  rw [eta0_lower_piece hlo hhi,
    show 4 * (y / r) = y * (4 / r) by ring,
    Real.log_mul hy.ne' (by positivity : (4 : ℝ) / r ≠ 0)]
  push_cast
  ring

lemma typeI_amplitude_upper_formula (r d y : ℝ) (c : ℂ)
    (hr : 0 < r) (hy : 0 < y) (hlo : 1 / 2 ≤ y / r) (hhi : y / r ≤ 1) :
    ((Real.log y : ℂ) + c * (Real.log d : ℂ)) * (eta0 (y / r) : ℂ) =
      -4 * ((Real.log y : ℂ) - (Real.log r : ℂ)) *
        ((Real.log y : ℂ) + c * (Real.log d : ℂ)) := by
  rw [eta0_upper_piece hlo hhi, Real.log_div hy.ne' hr.ne']
  push_cast
  ring

/-- The slope jumps at r/4, r/2, and r have weights 16, 16, and 4. -/
lemma typeI_jump_norm_budget (r X : ℝ) (A B C : ℂ) (hr : 0 < r)
    (hA : ‖A‖ ≤ X) (hB : ‖B‖ ≤ X) (hC : ‖C‖ ≤ X) :
    ‖(16 / (r : ℂ)) * A‖ + ‖(16 / (r : ℂ)) * B‖ + ‖(4 / (r : ℂ)) * C‖ ≤
      36 * X / r := by
  have h16 : ‖(16 : ℂ) / (r : ℂ)‖ = 16 / r := by
    simp [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have h4 : ‖(4 : ℂ) / (r : ℂ)‖ = 4 / r := by
    simp [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  simp only [norm_mul, h16, h4]
  calc
    _ ≤ (16 / r) * X + (16 / r) * X + (4 / r) * X := by gcongr
    _ = _ := by ring

/-- The exact one-sided slope at the left endpoint. -/
lemma typeI_left_endpoint_slope (r : ℝ) (hr : 0 < r) (b : ℂ) :
    4 / ((r / 4 : ℝ) : ℂ) *
      (2 * (Real.log (r / 4) : ℂ) + b + (Real.log (4 / r) : ℂ)) =
      (16 / (r : ℂ)) * ((Real.log (r / 4) : ℂ) + b) := by
  rw [Real.log_div hr.ne' (by norm_num), Real.log_div (by norm_num) hr.ne']
  push_cast
  field_simp
  ring

/-- The exact slope jump at the interior corner. -/
lemma typeI_middle_slope_jump (r : ℝ) (hr : 0 < r) (b : ℂ) :
    (-4 / ((r / 2 : ℝ) : ℂ) * (2 * (Real.log (r / 2) : ℂ) + b - (Real.log r : ℂ))) -
      (4 / ((r / 2 : ℝ) : ℂ) *
        (2 * (Real.log (r / 2) : ℂ) + b + (Real.log (4 / r) : ℂ))) =
      (-16 / (r : ℂ)) * ((Real.log (r / 2) : ℂ) + b) := by
  have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [Real.log_div hr.ne' (by norm_num), Real.log_div (by norm_num) hr.ne', hl4]
  push_cast
  field_simp
  ring

lemma typeI_right_endpoint_slope (r : ℝ) (b : ℂ) :
    -4 / (r : ℂ) * (2 * (Real.log r : ℂ) + b - (Real.log r : ℂ)) =
      (-4 / (r : ℂ)) * ((Real.log r : ℂ) + b) := by ring

end TaoFivePrimes

end


section

namespace TaoFivePrimes

open MeasureTheory

/-- Transfer a bound for sampled first differences of an integrable slope
to second differences of its primitive, without differentiability at corners.
The step identity is the integral form of absolute continuity. -/
theorem second_difference_from_integrated_slope
    (F g : ℝ → ℂ) (a V : ℝ) (N : ℕ)
    (hint : ∀ n : ℕ, IntervalIntegrable (fun t => g (a + 2 * n + t)) volume 0 2)
    (hstep : ∀ n : ℕ, F (a + 2 * (n + 1)) - F (a + 2 * n) =
      ∫ t in (0 : ℝ)..2, g (a + 2 * n + t))
    (hvar : ∀ t ∈ Set.Icc (0 : ℝ) 2,
      (∑ n ∈ Finset.range N, ‖g (a + 2 * (n + 1) + t) - g (a + 2 * n + t)‖) ≤ V) :
    (∑ n ∈ Finset.range N,
      ‖F (a + 2 * (n + 2)) - 2 * F (a + 2 * (n + 1)) + F (a + 2 * n)‖) ≤ 2 * V := by
  let H (n : ℕ) (t : ℝ) := g (a + 2 * (n + 1) + t) - g (a + 2 * n + t)
  have hH (n : ℕ) : IntervalIntegrable (H n) volume 0 2 := by
    simpa [H, Nat.cast_add, Nat.cast_one] using (hint (n + 1)).sub (hint n)
  have he (n : ℕ) : F (a + 2 * (n + 2)) - 2 * F (a + 2 * (n + 1)) + F (a + 2 * n) =
      ∫ t in (0 : ℝ)..2, H n t := by
    have hnext := hstep (n + 1)
    push_cast at hnext
    have hcur := hstep n
    have hsub := intervalIntegral.integral_sub (hint (n + 1)) (hint n)
    push_cast at hsub
    dsimp [H]
    rw [show (fun t : ℝ => g (a + 2 * (↑n + 1) + t) - g (a + 2 * ↑n + t)) =
      (fun t : ℝ => g (a + 2 * (↑n + 1) + t) - g (a + 2 * ↑n + t)) from rfl]
    rw [hsub, ← hnext, ← hcur]
    congr 1 <;> ring
  calc
    _ ≤ ∑ n ∈ Finset.range N, ∫ t in (0 : ℝ)..2, ‖H n t‖ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [he]
      exact intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ∫ t in (0 : ℝ)..2, ∑ n ∈ Finset.range N, ‖H n t‖ := by
      symm
      exact intervalIntegral.integral_finsetSum (fun n hn => (hH n).norm)
    _ ≤ ∫ t in (0 : ℝ)..2, V := by
      have hsum : IntervalIntegrable (fun t => ∑ n ∈ Finset.range N, ‖H n t‖) volume 0 2 := by
        have hs (s : Finset ℕ) : IntervalIntegrable (fun t => ∑ n ∈ s, ‖H n t‖) volume 0 2 := by
          induction s using Finset.induction with
          | empty => simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 2)
          | @insert n s hn ih =>
              simpa only [Finset.sum_insert hn] using (hH n).norm.add ih
        exact hs (Finset.range N)
      apply intervalIntegral.integral_mono_on (by norm_num)
        hsum intervalIntegrable_const
      exact hvar
    _ = 2 * V := by simp [mul_comm]

/-- Mathlib's bounded-variation quantity directly supplies the sampled bound. -/
theorem second_difference_from_bounded_variation
    (F g : ℝ → ℂ) (a V : ℝ) (N : ℕ) (hV : 0 ≤ V)
    (hint : ∀ n : ℕ, IntervalIntegrable (fun t => g (a + 2 * n + t)) volume 0 2)
    (hstep : ∀ n : ℕ, F (a + 2 * (n + 1)) - F (a + 2 * n) =
      ∫ t in (0 : ℝ)..2, g (a + 2 * n + t))
    (hvar : eVariationOn g Set.univ ≤ ENNReal.ofReal V) :
    (∑ n ∈ Finset.range N,
      ‖F (a + 2 * (n + 2)) - 2 * F (a + 2 * (n + 1)) + F (a + 2 * n)‖) ≤ 2 * V := by
  apply second_difference_from_integrated_slope F g a V N hint hstep
  intro t ht
  have hu : Monotone (fun n : ℕ => a + 2 * (n : ℝ) + t) := by
    intro m n hmn
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have h := (eVariationOn.sum_le (f := g) (s := Set.univ) (n := N)
    hu (fun _ => Set.mem_univ _)).trans hvar
  simp only [edist_dist, dist_eq_norm, Nat.cast_add, Nat.cast_one] at h
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n hn => norm_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff hV).mp h

end TaoFivePrimes

end


section

namespace TaoFivePrimes

/-- A real-valued increment budget controls the full metric variation. -/
theorem variation_le_of_increment_control (g : ℝ → ℂ) (B : ℝ → ℝ)
    (s : Set ℝ) (V : ℝ)
    (hstep : ∀ u ∈ s, ∀ v ∈ s, u ≤ v → ‖g v - g u‖ ≤ B v - B u)
    (hrange : ∀ u ∈ s, ∀ v ∈ s, B v - B u ≤ V) :
    eVariationOn g s ≤ ENNReal.ofReal V := by
  apply iSup_le
  rintro ⟨N, u, hu, hus⟩
  simp only [edist_dist, dist_eq_norm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n hn => norm_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ n ∈ Finset.range N, (B (u (n + 1)) - B (u n)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hstep _ (hus n) _ (hus (n + 1)) (hu (Nat.le_succ n))
    _ = B (u N) - B (u 0) := by
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, ih]; ring
    _ ≤ V := hrange _ (hus 0) _ (hus N)

/-- A single right-continuous slope jump contributes at most its norm. -/
theorem variation_step_le (a : ℝ) (z : ℂ) :
    eVariationOn (fun t : ℝ => if t < a then 0 else z) Set.univ ≤ ENNReal.ofReal ‖z‖ := by
  apply variation_le_of_increment_control _ (fun t : ℝ => if t < a then 0 else ‖z‖)
  · intro u hu v hv huv
    split_ifs <;> simp_all <;> linarith
  · intro u hu v hv
    split_ifs <;> simp_all <;> linarith [norm_nonneg z]

/-- Summing two finite variation budgets preserves their explicit constants. -/
theorem variation_add_budget (f g : ℝ → ℂ) (s : Set ℝ) (V W : ℝ)
    (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hf : eVariationOn f s ≤ ENNReal.ofReal V)
    (hg : eVariationOn g s ≤ ENNReal.ofReal W) :
    eVariationOn (fun t => f t + g t) s ≤ ENNReal.ofReal (V + W) := by
  apply iSup_le
  rintro ⟨N, u, hu, hus⟩
  have hf' := (eVariationOn.sum_le (f := f) (n := N) hu hus).trans hf
  have hg' := (eVariationOn.sum_le (f := g) (n := N) hu hus).trans hg
  simp only [edist_dist, dist_eq_norm] at hf' hg' ⊢
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n hn => norm_nonneg _)] at hf' hg' ⊢
  have hfR := (ENNReal.ofReal_le_ofReal_iff hV).mp hf'
  have hgR := (ENNReal.ofReal_le_ofReal_iff hW).mp hg'
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ n ∈ Finset.range N, (‖f (u (n + 1)) - f (u n)‖ + ‖g (u (n + 1)) - g (u n)‖) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [show f (u (n + 1)) + g (u (n + 1)) - (f (u n) + g (u n)) =
        (f (u (n + 1)) - f (u n)) + (g (u (n + 1)) - g (u n)) by ring]
      exact norm_add_le _ _
    _ ≤ V + W := by rw [Finset.sum_add_distrib]; exact add_le_add hfR hgR

/-- Variable derivative bounds control increments, using one-sided mean value
comparison rather than a smoothness assumption at interval endpoints. -/
theorem norm_sub_le_of_derivative_control (g g' : ℝ → ℂ) (B B' : ℝ → ℝ)
    (a b : ℝ) (hab : a ≤ b)
    (hg : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
    (hB : ∀ t ∈ Set.Icc a b, HasDerivAt B (B' t) t)
    (hbound : ∀ t ∈ Set.Icc a b, ‖g' t‖ ≤ B' t) :
    ‖g b - g a‖ ≤ B b - B a := by
  apply image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun t => g t - g a) (f' := g')
    (B := fun t => B t - B a) (B' := B') (a := a) (b := b)
    (fun t ht => ((hg t ht).sub_const (g a)).continuousAt.continuousWithinAt)
    (fun t ht => ((hg t ⟨ht.1, ht.2.le⟩).sub_const (g a)).hasDerivWithinAt)
    (by simp)
    (fun t ht => ((hB t ht).sub_const (B a)).continuousAt.continuousWithinAt)
    (fun t ht => ((hB t ⟨ht.1, ht.2.le⟩).sub_const (B a)).hasDerivWithinAt)
    (fun t ht => hbound t ⟨ht.1, ht.2.le⟩)
  exact ⟨hab, le_rfl⟩

/-- Smooth-piece variation with a nonconstant, integrable curvature budget. -/
theorem variation_interval_of_derivative_control (g g' : ℝ → ℂ) (B B' : ℝ → ℝ)
    (a b : ℝ)
    (hg : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
    (hB : ∀ t ∈ Set.Icc a b, HasDerivAt B (B' t) t)
    (hbound : ∀ t ∈ Set.Icc a b, ‖g' t‖ ≤ B' t)
    (hmono : MonotoneOn B (Set.Icc a b)) :
    eVariationOn g (Set.Icc a b) ≤ ENNReal.ofReal (B b - B a) := by
  apply variation_le_of_increment_control g B
  · intro u hu v hv huv
    have hsub : Set.Icc u v ⊆ Set.Icc a b := by
      intro t ht
      exact ⟨hu.1.trans ht.1, ht.2.trans hv.2⟩
    exact norm_sub_le_of_derivative_control g g' B B' u v huv
      (fun t ht => hg t (hsub ht)) (fun t ht => hB t (hsub ht))
      (fun t ht => hbound t (hsub ht))
  · intro u hu v hv
    have hab : a ≤ b := hu.1.trans hu.2
    have h1 := hmono hu ⟨hab, le_rfl⟩ hu.2
    have h2 := hmono ⟨le_rfl, hab⟩ hv hv.1
    have h3 := hmono hv ⟨hab, le_rfl⟩ hv.2
    have h4 := hmono ⟨le_rfl, hab⟩ hu hu.1
    linarith

lemma variation_sub_constant (f : ℝ → ℂ) (s : Set ℝ) (z : ℂ) :
    eVariationOn (fun t => f t - z) s = eVariationOn f s := by
  simp only [eVariationOn, edist_dist, dist_eq_norm, sub_sub_sub_cancel_right]

/-- Clamping a smooth piece to its interval does not increase variation. -/
lemma variation_clamp_le (f : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b) :
    eVariationOn (fun t => f (max a (min b t))) Set.univ ≤ eVariationOn f (Set.Icc a b) := by
  apply eVariationOn.comp_le_of_monotoneOn f
  · intro u hu v hv huv
    exact max_le_max_left a (min_le_min_left b huv)
  · intro t ht
    exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

noncomputable def joinedSlope (L R : ℝ → ℂ) (a b c y : ℝ) : ℂ :=
  if y < a then 0 else if y < b then L y else if y < c then R y else 0

/-- Clamped smooth pieces plus their three jumps give the exact zero extension. -/
lemma joinedSlope_decomposition (L R : ℝ → ℂ) (a b c y : ℝ)
    (hab : a ≤ b) (hbc : b ≤ c) :
    joinedSlope L R a b c y =
      (L (max a (min b y)) - L a) + (R (max b (min c y)) - R b) +
      (if y < a then 0 else L a) + (if y < b then 0 else R b - L b) +
      (if y < c then 0 else -R c) := by
  unfold joinedSlope
  by_cases ha : y < a
  · have hb : y < b := ha.trans_le hab
    have hc : y < c := hb.trans_le hbc
    simp [ha, hb, hc, min_eq_right hb.le, min_eq_right hc.le,
      max_eq_left ha.le, max_eq_left hb.le]
  · have hay : a ≤ y := le_of_not_gt ha
    by_cases hb : y < b
    · have hc : y < c := hb.trans_le hbc
      simp [ha, hb, hc, min_eq_right hb.le, min_eq_right hc.le,
        max_eq_right hay, max_eq_left hb.le]
    · have hby : b ≤ y := le_of_not_gt hb
      by_cases hc : y < c
      · simp only [ha, hb, hc, ↓reduceIte, min_eq_left hby, max_eq_right hab,
          min_eq_right hc.le, max_eq_right hby]
        ring
      · have hcy : c ≤ y := le_of_not_gt hc
        simp only [ha, hb, hc, ↓reduceIte, min_eq_left hby, max_eq_right hab,
          min_eq_left hcy, max_eq_right hbc]
        ring

theorem joinedSlope_variation_budget (L R : ℝ → ℂ) (a b c V W : ℝ)
    (hab : a ≤ b) (hbc : b ≤ c) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hL : eVariationOn L (Set.Icc a b) ≤ ENNReal.ofReal V)
    (hR : eVariationOn R (Set.Icc b c) ≤ ENNReal.ofReal W) :
    eVariationOn (joinedSlope L R a b c) Set.univ ≤
      ENNReal.ofReal (V + W + ‖L a‖ + ‖R b - L b‖ + ‖R c‖) := by
  have h1 : eVariationOn (fun y => L (max a (min b y)) - L a) Set.univ ≤ ENNReal.ofReal V := by
    rw [variation_sub_constant]
    exact (variation_clamp_le L a b hab).trans hL
  have h2 : eVariationOn (fun y => R (max b (min c y)) - R b) Set.univ ≤ ENNReal.ofReal W := by
    rw [variation_sub_constant]
    exact (variation_clamp_le R b c hbc).trans hR
  have h12 := variation_add_budget _ _ Set.univ V W hV hW h1 h2
  have h3 := variation_add_budget _ _ Set.univ (V + W) ‖L a‖ (by positivity)
    (norm_nonneg _) h12 (variation_step_le a (L a))
  have h4 := variation_add_budget _ _ Set.univ (V + W + ‖L a‖) ‖R b - L b‖ (by positivity)
    (norm_nonneg _) h3 (variation_step_le b (R b - L b))
  have h5 := variation_add_budget _ _ Set.univ (V + W + ‖L a‖ + ‖R b - L b‖) ‖-R c‖ (by positivity)
    (norm_nonneg _) h4 (variation_step_le c (-R c))
  have he := funext (fun y => joinedSlope_decomposition L R a b c y hab hbc)
  rw [he]
  simpa only [norm_neg] using h5

end TaoFivePrimes

end


section

namespace TaoFivePrimes

/-- Variation of one logarithmic slope piece, with its inverse-square
curvature integrated exactly rather than replaced by a uniform bound. -/
theorem log_slope_variation_bound (a b X k : ℝ) (c : ℂ)
    (ha : 0 < a) (hX : 0 ≤ X)
    (hcoef : ∀ y ∈ Set.Icc a b, ‖(Real.log y : ℂ) + c‖ ≤ X)
    (hcut : ∀ y ∈ Set.Icc a b, |Real.log y + k| ≤ 3 / 4) :
    eVariationOn (fun y : ℝ => 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c + (k : ℂ)))
      (Set.Icc a b) ≤ ENNReal.ofReal ((4 * X + 11) * (a⁻¹ - b⁻¹)) := by
  let C : ℝ := 4 * X + 11
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hB (y : ℝ) (hy : y ≠ 0) :
      HasDerivAt (fun t : ℝ => -C / t) (C / y ^ 2) y := by
    have h := (hasDerivAt_const y (-C)).div (hasDerivAt_id y) hy
    convert h using 1 <;> first | rfl | simp
  have h := variation_interval_of_derivative_control
    (fun y : ℝ => 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c + (k : ℂ)))
    (fun y : ℝ => 4 / (y : ℂ) ^ 2 * (2 - 2 * (Real.log y : ℂ) - c - (k : ℂ)))
    (fun y : ℝ => -C / y) (fun y : ℝ => C / y ^ 2) a b
    (fun y hy => log_product_derivative_hasDerivAt y (ne_of_gt (ha.trans_le hy.1)) c k)
    (fun y hy => hB y (ne_of_gt (ha.trans_le hy.1)))
    (by
      intro y hy
      have hh := typeI_curvature_majorant y X (Real.log y + k) ((Real.log y : ℂ) + c)
        (ha.trans_le hy.1) (hcoef y hy) (hcut y hy)
      convert hh using 1 <;> first | rfl | (push_cast; congr 1; ring))
    (by
      intro u hu v hv huv
      dsimp
      rw [neg_div, neg_div]
      exact neg_le_neg (div_le_div_of_nonneg_left hC (ha.trans_le hu.1) huv))
  convert h using 1
  congr 1
  dsimp [C]
  ring

lemma abs_log_ratio_short (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hba : b ≤ 2 * a) :
    |Real.log b - Real.log a| ≤ 3 / 4 := by
  have hb : 0 < b := ha.trans_le hab
  have hlog0 : 0 ≤ Real.log b - Real.log a := sub_nonneg.mpr (Real.log_le_log ha hab)
  rw [abs_of_nonneg hlog0, ← Real.log_div hb.ne' ha.ne']
  have hlog2 := Real.log_le_log (div_pos hb ha) ((div_le_iff₀ ha).mpr (by linarith : b ≤ 2 * a))
  linarith [Real.log_two_lt_d9]

lemma lower_cutoff_log_bound (r y : ℝ) (hr : 0 < r) (hy : y ∈ Set.Icc (r / 4) (r / 2)) :
    |Real.log y + Real.log (4 / r)| ≤ 3 / 4 := by
  have h := abs_log_ratio_short (r / 4) y (by positivity) hy.1 (by linarith [hy.2])
  have he : Real.log (4 / r) = -Real.log (r / 4) := by
    rw [Real.log_div (by norm_num) hr.ne', Real.log_div hr.ne' (by norm_num)]
    ring
  simpa only [he, sub_eq_add_neg] using h

lemma upper_cutoff_log_bound (r y : ℝ) (hr : 0 < r) (hy : y ∈ Set.Icc (r / 2) r) :
    |Real.log y + -Real.log r| ≤ 3 / 4 := by
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity : 0 < r / 2) hy.1
  have h := abs_log_ratio_short y r hy0 hy.2 (by linarith [hy.1])
  simpa only [← sub_eq_add_neg, abs_sub_comm] using h

lemma variation_neg (f : ℝ → ℂ) (s : Set ℝ) :
    eVariationOn (fun y => -f y) s = eVariationOn f s := by
  simp only [eVariationOn, edist_dist, dist_eq_norm, neg_sub_neg, norm_sub_rev]

noncomputable def typeIPiecewiseSlope (r d : ℝ) (c : ℂ) : ℝ → ℂ :=
  joinedSlope
    (fun y => 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c * (Real.log d : ℂ) + (Real.log (4 / r) : ℂ)))
    (fun y => -4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c * (Real.log d : ℂ) - (Real.log r : ℂ)))
    (r / 4) (r / 2) r

/-- The actual zero-extended piecewise slope has the required variation budget. -/
theorem typeI_piecewise_slope_variation (r d : ℝ) (c : ℂ)
    (hr : 4 ≤ r) (hd : 1 ≤ d) (hc : ‖c‖ ≤ 1) :
    eVariationOn (typeIPiecewiseSlope r d c) Set.univ ≤
      ENNReal.ofReal (48 * Real.log (4 * (d * r)) / r) := by
  have hr0 : 0 < r := by linarith
  have hd0 : 0 < d := by linarith
  let X := Real.log (d * r)
  let C := 4 * X + 11
  let b0 : ℂ := c * (Real.log d : ℂ)
  let L (y : ℝ) := 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + b0 + (Real.log (4 / r) : ℂ))
  let R (y : ℝ) := -4 / (y : ℂ) * (2 * (Real.log y : ℂ) + b0 - (Real.log r : ℂ))
  have hX : 0 ≤ X := Real.log_nonneg (by nlinarith)
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hcoef (y : ℝ) (hy : y ∈ Set.Icc (r / 4) r) : ‖(Real.log y : ℂ) + b0‖ ≤ X := by
    apply typeI_log_coefficient_bound (d * r) d y c hd (by linarith [hy.1]) _ hc
    exact mul_le_mul_of_nonneg_left hy.2 hd0.le
  have hL : eVariationOn L (Set.Icc (r / 4) (r / 2)) ≤ ENNReal.ofReal (2 * C / r) := by
    have h := log_slope_variation_bound (r / 4) (r / 2) X (Real.log (4 / r)) b0
      (by positivity) hX (fun y hy => hcoef y ⟨hy.1, by linarith [hy.2]⟩)
      (fun y hy => lower_cutoff_log_bound r y hr0 hy)
    convert h using 1
    congr 1
    dsimp [C]
    field_simp
    ring
  have hR : eVariationOn R (Set.Icc (r / 2) r) ≤ ENNReal.ofReal (C / r) := by
    let P (y : ℝ) := 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + b0 + ((-Real.log r : ℝ) : ℂ))
    have he : R = fun y => -P y := by
      funext y
      dsimp [R, P]
      push_cast
      ring
    rw [he, variation_neg]
    have h := log_slope_variation_bound (r / 2) r X (-Real.log r) b0
      (by positivity) hX (fun y hy => hcoef y ⟨by linarith [hy.1], hy.2⟩)
      (fun y hy => upper_cutoff_log_bound r y hr0 hy)
    convert h using 1
    congr 1
    dsimp [C]
    field_simp
    ring
  have hj : ‖L (r / 4)‖ + ‖R (r / 2) - L (r / 2)‖ + ‖R r‖ ≤ 36 * X / r := by
    have h := typeI_jump_norm_budget r X
      ((Real.log (r / 4) : ℂ) + b0) ((Real.log (r / 2) : ℂ) + b0)
      ((Real.log r : ℂ) + b0) hr0
      (hcoef _ ⟨le_rfl, by linarith⟩) (hcoef _ ⟨by linarith, by linarith⟩)
      (hcoef _ ⟨by linarith, le_rfl⟩)
    dsimp [L, R]
    rw [typeI_left_endpoint_slope r hr0 b0, typeI_middle_slope_jump r hr0 b0,
      typeI_right_endpoint_slope r b0]
    simpa only [neg_div, neg_mul, norm_neg] using h
  have h := joinedSlope_variation_budget L R (r / 4) (r / 2) r (2 * C / r) (C / r)
    (by linarith) (by linarith) (by positivity) (by positivity) hL hR
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hb := typeI_curvature_and_jump_budget (d * r) r (mul_pos hd0 hr0) hr0
  have he : 2 * C / r + C / r = (12 * X + 33) / r := by dsimp [C]; ring
  rw [he]
  dsimp [X] at hj ⊢
  linarith

end TaoFivePrimes

end


section

namespace TaoFivePrimes

open Filter
open scoped Topology

@[fun_prop] lemma eta0_continuous : Continuous eta0 := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t < 1 / 4
  · have he : eta0 =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_lt_nhds ht] with u hu
      exact eta0_zero_below_quarter hu.le
    exact (continuousAt_congr he).mpr continuousAt_const
  · have ht0 : 0 < t := by linarith
    have he : eta0 =ᶠ[𝓝 t] (fun u : ℝ => 4 * max 0 (Real.log 2 - |Real.log (2 * u)|)) := by
      filter_upwards [eventually_gt_nhds ht0] with u hu
      simp [eta0, hu]
    apply (continuousAt_congr he).mpr
    fun_prop (disch := positivity)

noncomputable def typeIRealAmplitude (r d : ℝ) (c : ℂ) (y : ℝ) : ℂ :=
  ((Real.log y : ℂ) + c * (Real.log d : ℂ)) * (eta0 (y / r) : ℂ)

lemma typeI_real_amplitude_continuous (r d : ℝ) (c : ℂ) (hr : 0 < r) :
    Continuous (typeIRealAmplitude r d c) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y = 0
  · subst y
    have he : typeIRealAmplitude r d c =ᶠ[𝓝 0] (fun _ => (0 : ℂ)) := by
      filter_upwards [eventually_lt_nhds (show (0 : ℝ) < r / 4 by positivity)] with t ht
      have hcut : eta0 (t / r) = 0 := eta0_zero_below_quarter
        ((div_le_iff₀ hr).mpr (by linarith))
      simp [typeIRealAmplitude, hcut]
    exact (continuousAt_congr he).mpr continuousAt_const
  · unfold typeIRealAmplitude
    have hcut : Continuous (fun y : ℝ => (eta0 (y / r) : ℂ)) := by fun_prop
    exact (((Real.continuousAt_log hy).ofReal).add continuousAt_const).mul hcut.continuousAt

/-- The right-hand slope agrees at all three corners with the chosen
right-continuous piecewise derivative. -/
theorem typeI_real_amplitude_right_deriv (r d y : ℝ) (c : ℂ) (hr : 0 < r) :
    HasDerivWithinAt (typeIRealAmplitude r d c) (typeIPiecewiseSlope r d c y) (Set.Ici y) y := by
  have hzero (t : ℝ) (ht : t ≤ r / 4) : typeIRealAmplitude r d c t = 0 := by
    have h := eta0_zero_below_quarter ((div_le_iff₀ hr).mpr (by linarith : t ≤ 1 / 4 * r))
    simp [typeIRealAmplitude, h]
  have hzero' (t : ℝ) (ht : r ≤ t) : typeIRealAmplitude r d c t = 0 := by
    have h := eta0_zero_above_one ((le_div_iff₀ hr).mpr (by simpa using ht))
    simp [typeIRealAmplitude, h]
  unfold typeIPiecewiseSlope joinedSlope
  split_ifs with ha hb hc
  · apply (hasDerivWithinAt_const y (Set.Ici y) (0 : ℂ)).congr_of_eventuallyEq_of_mem
    · filter_upwards [(eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with t ht
      exact hzero t ht.le
    · exact Set.mem_Ici.mpr le_rfl
  · have hay : r / 4 ≤ y := le_of_not_gt ha
    have hy : 0 < y := lt_of_lt_of_le (by positivity) hay
    apply (log_product_hasDerivAt y hy.ne' (c * (Real.log d : ℂ)) (Real.log (4 / r))).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with t ht ht'
      change y ≤ t at ht
      exact typeI_amplitude_lower_formula r d t c hr (hy.trans_le ht)
        ((le_div_iff₀ hr).mpr (by linarith)) ((div_le_iff₀ hr).mpr (by linarith))
    · exact Set.mem_Ici.mpr le_rfl
  · have hby : r / 2 ≤ y := le_of_not_gt hb
    have hy : 0 < y := lt_of_lt_of_le (by positivity) hby
    have h := (log_product_hasDerivAt y hy.ne' (c * (Real.log d : ℂ)) (-Real.log r)).neg
    have hd : HasDerivAt
        (fun t : ℝ => -4 * ((Real.log t : ℂ) - (Real.log r : ℂ)) *
          ((Real.log t : ℂ) + c * (Real.log d : ℂ)))
        (-4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c * (Real.log d : ℂ) - (Real.log r : ℂ))) y := by
      have he : (fun t : ℝ => -4 * ((Real.log t : ℂ) - (Real.log r : ℂ)) *
          ((Real.log t : ℂ) + c * (Real.log d : ℂ))) =
          -(fun t : ℝ => 4 * ((Real.log t : ℂ) + (-Real.log r : ℂ)) *
            ((Real.log t : ℂ) + c * (Real.log d : ℂ))) := by
        funext t
        simp only [Pi.neg_apply]
        ring
      rw [he]
      convert h using 1 <;> first | rfl | (push_cast; ring)
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hc).filter_mono nhdsWithin_le_nhds] with t ht ht'
      change y ≤ t at ht
      exact typeI_amplitude_upper_formula r d t c hr (hy.trans_le ht)
        ((le_div_iff₀ hr).mpr (by linarith)) ((div_le_iff₀ hr).mpr (by linarith))
    · exact Set.mem_Ici.mpr le_rfl
  · apply (hasDerivWithinAt_const y (Set.Ici y) (0 : ℂ)).congr_of_eventuallyEq_of_mem
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact hzero' t ((le_of_not_gt hc).trans ht)
    · exact Set.mem_Ici.mpr le_rfl

open MeasureTheory

lemma intervalIntegrable_piecewise_local (f g : ℝ → ℂ) (s : Set ℝ)
    [DecidablePred (· ∈ s)] (hs : MeasurableSet s) (a b : ℝ)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (s.piecewise f g) volume a b :=
  ⟨Integrable.piecewise hs hf.1.integrableOn hg.1.integrableOn,
    Integrable.piecewise hs hf.2.integrableOn hg.2.integrableOn⟩

lemma typeI_slope_intervalIntegrable (r d : ℝ) (c : ℂ) (hr : 0 < r) (a b : ℝ) :
    IntervalIntegrable (typeIPiecewiseSlope r d c) volume a b := by
  let L (y : ℝ) := 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c * (Real.log d : ℂ) + (Real.log (4 / r) : ℂ))
  let R (y : ℝ) := -4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c * (Real.log d : ℂ) - (Real.log r : ℂ))
  have hL : ContinuousOn L (Set.Icc (r / 4) (r / 2)) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy.1
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    have hyN : y ≠ 0 := hy0.ne'
    apply ContinuousAt.continuousWithinAt
    dsimp [L]
    fun_prop (disch := assumption)
  have hR : ContinuousOn R (Set.Icc (r / 2) r) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy.1
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    have hyN : y ≠ 0 := hy0.ne'
    apply ContinuousAt.continuousWithinAt
    dsimp [R]
    fun_prop (disch := assumption)
  have hLc : Continuous (fun y => L (max (r / 4) (min (r / 2) y))) :=
    hL.comp_continuous (by fun_prop) (fun y => ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩)
  have hRc : Continuous (fun y => R (max (r / 2) (min r y))) :=
    hR.comp_continuous (by fun_prop) (fun y => ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩)
  have hstep (u : ℝ) (z : ℂ) : IntervalIntegrable (fun y => if y < u then 0 else z) volume a b :=
    intervalIntegrable_piecewise_local (fun _ => 0) (fun _ => z) (Set.Iio u)
      measurableSet_Iio a b intervalIntegrable_const intervalIntegrable_const
  have he : typeIPiecewiseSlope r d c = fun y =>
      (L (max (r / 4) (min (r / 2) y)) - L (r / 4)) +
      (R (max (r / 2) (min r y)) - R (r / 2)) +
      (if y < r / 4 then 0 else L (r / 4)) +
      (if y < r / 2 then 0 else R (r / 2) - L (r / 2)) + (if y < r then 0 else -R r) :=
    funext (fun y => joinedSlope_decomposition L R (r / 4) (r / 2) r y (by linarith) (by linarith))
  rw [he]
  exact (((((hLc.sub continuous_const).intervalIntegrable a b).add
    ((hRc.sub continuous_const).intervalIntegrable a b)).add (hstep _ _)).add (hstep _ _)).add (hstep _ _)

/-- Integral reconstruction of the literal cutoff amplitude, including corners. -/
theorem typeI_slope_integral (r d : ℝ) (c : ℂ) (hr : 0 < r) (a b : ℝ) (hab : a ≤ b) :
    (∫ y in a..b, typeIPiecewiseSlope r d c y) =
      typeIRealAmplitude r d c b - typeIRealAmplitude r d c a := by
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (typeI_real_amplitude_continuous r d c hr).continuousOn
  · intro y hy
    exact (typeI_real_amplitude_right_deriv r d y c hr).mono Set.Ioi_subset_Ici_self
  · exact typeI_slope_intervalIntegrable r d c hr a b

end TaoFivePrimes

end


section

namespace TaoFivePrimes

open MeasureTheory

theorem typeI_finite_second_difference_bound (r d a : ℝ) (c : ℂ) (N : ℕ)
    (hr : 4 ≤ r) (hd : 1 ≤ d) (hc : ‖c‖ ≤ 1) :
    (∑ n ∈ Finset.range N,
      ‖typeIRealAmplitude r d c (a + 2 * (n + 2)) -
        2 * typeIRealAmplitude r d c (a + 2 * (n + 1)) + typeIRealAmplitude r d c (a + 2 * n)‖) ≤
      96 * Real.log (4 * (d * r)) / r := by
  have hr0 : 0 < r := by linarith
  have hlog : 0 ≤ Real.log (4 * (d * r)) := Real.log_nonneg (by nlinarith)
  have h := second_difference_from_bounded_variation (typeIRealAmplitude r d c)
    (typeIPiecewiseSlope r d c) a (48 * Real.log (4 * (d * r)) / r) N (by positivity)
    (by
      intro n
      have hi := (typeI_slope_intervalIntegrable r d c hr0 (a + 2 * n) (a + 2 * n + 2)).comp_add_left (a + 2 * n)
      simpa only [sub_self, add_sub_cancel_left] using hi)
    (by
      intro n
      rw [intervalIntegral.integral_comp_add_left]
      simp only [add_zero]
      rw [typeI_slope_integral r d c hr0 _ _ (by linarith)]
      congr 1
      congr 1
      ring)
    (typeI_piecewise_slope_variation r d c hr hd hc)
  convert h using 1
  ring

/-- Passing from finite prefixes to the whole odd integer lattice. The shift
by one includes the possible first nonzero second difference at index -1. -/
theorem odd_integer_second_difference_of_prefix_bound (F : ℝ → ℂ) (B : ℝ)
    (hzero : ∀ y ≤ 1, F y = 0)
    (hprefix : ∀ N : ℕ, (∑ n ∈ Finset.range N,
      ‖F (-1 + 2 * (n + 2)) - 2 * F (-1 + 2 * (n + 1)) + F (-1 + 2 * n)‖) ≤ B) :
    (∑' n : ℤ, ‖F (2 * (n + 2) + 1) - 2 * F (2 * (n + 1) + 1) + F (2 * n + 1)‖) ≤ B := by
  let D (n : ℤ) := ‖F (2 * (n + 2) + 1) - 2 * F (2 * (n + 1) + 1) + F (2 * n + 1)‖
  let G (n : ℤ) := D (n - 1)
  have he (n : ℕ) : G n =
      ‖F (-1 + 2 * (n + 2)) - 2 * F (-1 + 2 * (n + 1)) + F (-1 + 2 * n)‖ := by
    dsimp [G, D]
    push_cast
    congr 1 <;> congr 1 <;> congr 1 <;> ring
  have hp : ∀ N : ℕ, ∑ n ∈ Finset.range N, G n ≤ B := by
    intro N
    simpa only [he] using hprefix N
  have hn (n : ℕ) : G (-(n + 1)) = 0 := by
    have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    dsimp [G, D]
    push_cast
    rw [hzero _ (by linarith), hzero _ (by linarith), hzero _ (by linarith)]
    simp
  have hs : Summable (fun n : ℕ => G n) := summable_of_sum_range_le (fun n => norm_nonneg _) hp
  have hsneg : Summable (fun n : ℕ => G (-(n + 1))) := by simp only [hn]; exact summable_zero
  have hsum := tsum_of_nat_of_neg_add_one hs hsneg
  simp only [hn, tsum_zero, add_zero] at hsum
  have hshift : (∑' n : ℤ, G n) = ∑' n : ℤ, D n := by
    exact (Equiv.addRight (-1 : ℤ)).tsum_eq D
  change (∑' n : ℤ, D n) ≤ B
  rw [← hshift, hsum]
  exact Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) hp

theorem typeI_integer_second_difference_bound (r d : ℝ) (c : ℂ)
    (hr : 4 ≤ r) (hd : 1 ≤ d) (hc : ‖c‖ ≤ 1) :
    (∑' n : ℤ, ‖typeIRealAmplitude r d c (2 * (n + 2) + 1) -
      2 * typeIRealAmplitude r d c (2 * (n + 1) + 1) + typeIRealAmplitude r d c (2 * n + 1)‖) ≤
      96 * Real.log (4 * (d * r)) / r := by
  apply odd_integer_second_difference_of_prefix_bound
  · intro y hy
    have hr0 : 0 < r := by linarith
    have hcut := eta0_zero_below_quarter ((div_le_iff₀ hr0).mpr (by linarith : y ≤ 1 / 4 * r))
    simp [typeIRealAmplitude, hcut]
  · intro N
    exact typeI_finite_second_difference_bound r d (-1) c N hr hd hc

/-- The formerly assumed concrete Type I variation estimate, now proved. -/
theorem typeI_actual_discrete_variation (x d : ℝ) (c : ℂ)
    (hd : 1 ≤ d) (hdx : 4 * d ≤ x) (hc : ‖c‖ ≤ 1) :
    (∑' n : ℤ, ‖typeIOddAmplitude x d c (n + 2) -
      2 * typeIOddAmplitude x d c (n + 1) + typeIOddAmplitude x d c n‖) ≤
      96 * Real.log (4 * x) / x * d := by
  have hd0 : 0 < d := by linarith
  have hx0 : 0 < x := by linarith
  have hr : 4 ≤ x / d := (le_div_iff₀ hd0).mpr hdx
  have h := typeI_integer_second_difference_bound (x / d) d c hr hd hc
  have he (n : ℤ) : typeIOddAmplitude x d c n = typeIRealAmplitude (x / d) d c (2 * n + 1) := by
    unfold typeIOddAmplitude typeIRealAmplitude
    push_cast
    congr 2
    field_simp
  simp_rw [he]
  have hl : d * (x / d) = x := by field_simp
  rw [hl] at h
  convert h using 1 <;> first | rfl | (push_cast; field_simp)

end TaoFivePrimes

end


section

namespace TaoFivePrimes

/-- Full Type I analytic estimate for the literal odd-lattice amplitudes.
There is no Fourier-decay, smoothness, or variation hypothesis left. -/
theorem unit_typeI_actual_sum
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ) (s : Finset ℕ) (c : ℕ → ℂ)
    (hx : 1 ≤ x) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUVx : U * V ≤ x / 4) (hUVq : U * V < (q : ℝ) - 1) (ha : a.natAbs = 1)
    (hs : ∀ d ∈ s, 0 < d ∧ (d : ℝ) ≤ U * V ∧ d.Coprime 2)
    (hc : ∀ d ∈ s, ‖c d‖ ≤ 1)
    (hphase : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ d ∈ s, ‖∑' n : ℤ, typeIOddAmplitude x d (c d) n *
      expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ))‖) ≤
      (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
        Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  simp_rw [norm_odd_fourier_eq_geometric]
  apply unit_typeI_from_discrete_variation x alpha beta U V a q s
    (fun d => typeIOddAmplitude x d (c d)) hx hU hV hUVq ha hs hphase hbeta
  · intro d hd
    exact typeIOddAmplitude_finite x d (c d) (by linarith) (by exact_mod_cast (hs d hd).1)
  · intro d hd
    apply typeI_actual_discrete_variation x d (c d)
    · exact_mod_cast (hs d hd).1
    · have hdUV := (hs d hd).2.1
      linarith
    · exact hc d hd

end TaoFivePrimes

end


section

namespace TaoFivePrimes

/-- The complete Type I bound expressed in the public decomposition interface. -/
theorem theorem51_typeI_bound
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ) (c : ℕ → ℂ)
    (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUVx : U * V ≤ x / 4) (hUVq : U * V < (q : ℝ) - 1)
    (ha : a.natAbs = 1)
    (hc : ∀ d ∈ theorem51Divisors U V, ‖c d‖ ≤ 1)
    (hphase : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    theorem51TypeI x alpha U V c ≤
      (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
        Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  have hUV : 0 ≤ U * V := mul_nonneg (by linarith) (by linarith)
  have hm := mul_nonneg (show 0 ≤ U - 40 by linarith) (show 0 ≤ V - 40 by linarith)
  have hx : 1 ≤ x := by nlinarith
  apply unit_typeI_actual_sum x alpha beta U V a q (theorem51Divisors U V) c
    hx hU hV hUVx hUVq ha _ hc hphase hbeta
  intro d hd
  obtain ⟨hd, hodd⟩ := Finset.mem_filter.mp hd
  obtain ⟨hd1, hdUV⟩ := Finset.mem_Icc.mp hd
  refine ⟨hd1, ?_, hodd⟩
  exact (Nat.cast_le.mpr hdUV).trans (Nat.floor_le hUV)

end TaoFivePrimes

end

open TaoFivePrimes
theorem solution
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ) (c : ℕ → ℂ)
    (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUVx : U * V ≤ x / 4) (hUVq : U * V < (q : ℝ) - 1)
    (ha : a.natAbs = 1)
    (hc : ∀ d ∈ theorem51Divisors U V, ‖c d‖ ≤ 1)
    (hphase : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    theorem51TypeI x alpha U V c ≤
      (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
        Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  exact theorem51_typeI_bound x alpha beta U V a q c hU hV hUVx hUVq ha hc hphase hbeta
#print axioms solution


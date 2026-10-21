-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P03.lemma8_polynomialCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:13:24.368107+00:00
-- url     : https://prove2.me/submissions/5f32fc59-8f44-4deb-a189-a6998377eb4d

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate Matrix

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace


lemma g59a_disk (k : ℕ) (a : ℕ → ℝ) (M : ℝ)
    (hM : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |∑ i ∈ Finset.Icc 1 k, a i * t ^ i| ≤ M) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * z ^ i‖ ≤ (1 + Real.sqrt 2) ^ k * M := by
  set f : ℂ → ℂ := fun w => ∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * (w ^ (k - i) * ((w ^ 2 + 1) / 2) ^ i)
    with hf
  have hf_eq : ∀ w : ℂ, w ≠ 0 → f w = w ^ k * ∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * ((w + w⁻¹) / 2) ^ i := by
    intro w hw
    rw [hf, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
    have e1 : (w ^ 2 + 1) / 2 = w * ((w + w⁻¹) / 2) := by field_simp
    rw [e1, mul_pow, show w ^ k = w ^ (k - i) * w ^ i by rw [← pow_add, Nat.sub_add_cancel hik]]
    ring
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 ⟨by norm_num, by norm_num⟩)
  have hcircle : ∀ w : ℂ, w ∈ frontier (Metric.ball (0 : ℂ) 1) → ‖f w‖ ≤ M := by
    intro w hw
    rw [frontier_ball (0 : ℂ) one_ne_zero, mem_sphere_zero_iff_norm] at hw
    have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; norm_num at hw
    rw [hf_eq w hw0, norm_mul, norm_pow, hw, one_pow, one_mul]
    have hinv : w⁻¹ = conj w := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hw]; simp
    have hre : (w + w⁻¹) / 2 = ((w.re : ℝ) : ℂ) := by
      rw [hinv, Complex.add_conj]; push_cast; ring
    rw [hre]
    have : ∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * ((w.re : ℝ) : ℂ) ^ i =
        ((∑ i ∈ Finset.Icc 1 k, a i * w.re ^ i : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    have hb := Complex.abs_re_le_norm w
    rw [hw] at hb
    exact hM _ ⟨by linarith [neg_abs_le w.re], by linarith [le_abs_self w.re]⟩
  have hdiff : Differentiable ℂ f := by
    rw [hf]; fun_prop
  have hdisk : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖f w‖ ≤ M := by
    intro w hw
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
      hdiff.diffContOnCl hcircle ?_
    rw [closure_ball (0 : ℂ) one_ne_zero, mem_closedBall_zero_iff]; exact hw
  have key : ∀ w v : ℂ, w * v = 1 → w + v = 2 * z → ‖w‖ ≤ 1 →
      ‖∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * z ^ i‖ ≤ (1 + Real.sqrt 2) ^ k * M := by
    intro w v hwv hsum hw1
    have hw0 : w ≠ 0 := by intro h; rw [h, zero_mul] at hwv; exact zero_ne_one hwv
    have hv : v = w⁻¹ := by
      field_simp; rw [mul_comm]; exact hwv
    have hz' : z = (w + w⁻¹) / 2 := by rw [← hv]; linear_combination -hsum / 2
    set r := ‖w‖ with hr
    have hr0 : 0 < r := norm_pos_iff.mpr hw0
    have hvn : ‖v‖ = r⁻¹ := by rw [hv, norm_inv]
    have hle : ‖v‖ ≤ 2 + r := by
      have : v = (w + v) - w := by ring
      rw [this, hsum]
      calc ‖2 * z - w‖ ≤ ‖2 * z‖ + ‖w‖ := norm_sub_le _ _
        _ = 2 + r := by rw [norm_mul, hz, hr]; simp
    rw [hvn] at hle
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have h1 : 1 ≤ r * (2 + r) := by
      have := mul_le_mul_of_nonneg_left hle hr0.le
      rwa [mul_inv_cancel₀ hr0.ne'] at this
    have hrinv : r⁻¹ ≤ 1 + Real.sqrt 2 := by
      rw [inv_le_iff_one_le_mul₀ hr0]
      nlinarith [sq_nonneg (r + 1 - Real.sqrt 2)]
    have hfw := hdisk w hw1
    rw [hf_eq w hw0, norm_mul, norm_pow, ← hz'] at hfw
    have hrk : 0 < r ^ k := pow_pos hr0 k
    calc ‖∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * z ^ i‖ ≤ M / r ^ k := by
          rw [le_div_iff₀ hrk, mul_comm]; exact hfw
      _ = (r⁻¹) ^ k * M := by rw [inv_pow]; ring
      _ ≤ (1 + Real.sqrt 2) ^ k * M :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_nonneg.mpr hr0.le) hrinv k) hM0
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (z ^ 2 - 1) two_pos
  have hprod : (z + s) * (z - s) = 1 := by linear_combination -hs
  by_cases h1 : ‖z + s‖ ≤ 1
  · exact key (z + s) (z - s) hprod (by ring) h1
  · refine key (z - s) (z + s) (by rw [mul_comm]; exact hprod) (by ring) ?_
    have := congrArg norm hprod
    rw [norm_mul, norm_one] at this
    push Not at h1
    nlinarith [norm_nonneg (z - s)]

lemma g59a_geom (N : ℕ) (hN : N ≠ 0) (ω : ℂ) (hω : IsPrimitiveRoot ω N) (m : ℕ) :
    ∑ l ∈ Finset.range N, (ω ^ m) ^ l = if N ∣ m then (N : ℂ) else 0 := by
  by_cases h : N ∣ m
  · rw [if_pos h, (hω.pow_eq_one_iff_dvd m).mpr h]; simp
  · rw [if_neg h]
    have h1 : ω ^ m ≠ 1 := fun h' => h ((hω.pow_eq_one_iff_dvd m).mp h')
    rw [geom_sum_eq h1, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self, zero_div]

lemma g59a_cauchy (k : ℕ) (a : ℕ → ℝ) (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) (B : ℝ)
    (hB : ∀ z : ℂ, ‖z‖ = 1 → ‖∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * z ^ i‖ ≤ B) : |a j| ≤ B := by
  set N := k + 1 with hN
  have hN0 : N ≠ 0 := by omega
  set ω := Complex.exp (2 * Real.pi * Complex.I / N) with hωdef
  have hω : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N hN0
  have hωn : ‖ω‖ = 1 := hω.norm'_eq_one hN0
  have hsum : ∑ l ∈ Finset.range N, (∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * (ω ^ l) ^ i) *
      (ω ^ l) ^ (N - j) = (N : ℂ) * (a j : ℂ) := by
    have e : ∀ l, (∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * (ω ^ l) ^ i) * (ω ^ l) ^ (N - j) =
        ∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * (ω ^ (i + (N - j))) ^ l := by
      intro l; rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← pow_mul, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]; ring_nf
    simp only [e]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, g59a_geom N hN0 ω hω]
    rw [Finset.sum_eq_single j]
    · rw [if_pos (by rw [show j + (N - j) = N by omega])]; ring
    · intro i hi hij
      rw [if_neg, mul_zero]
      rintro ⟨c, hc⟩
      have hi' := Finset.mem_Icc.mp hi
      rcases c with _ | _ | c
      · omega
      · omega
      · have h2 : N * (c + 1 + 1) = N * c + 2 * N := by ring
        omega
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨hj, hjk⟩) h
  have hbound : ‖(N : ℂ) * (a j : ℂ)‖ ≤ N * B := by
    rw [← hsum]
    calc _ ≤ ∑ l ∈ Finset.range N, ‖(∑ i ∈ Finset.Icc 1 k, (a i : ℂ) * (ω ^ l) ^ i) *
          (ω ^ l) ^ (N - j)‖ := norm_sum_le _ _
      _ ≤ ∑ l ∈ Finset.range N, B := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [norm_mul, norm_pow, norm_pow, hωn, one_pow, one_pow, mul_one]
          exact hB _ (by rw [norm_pow, hωn, one_pow])
      _ = N * B := by simp
  rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs] at hbound
  have : (0 : ℝ) < N := by positivity
  exact le_of_mul_le_mul_left hbound this

theorem g59a_poly (k : ℕ) (a : ℕ → ℝ) (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1,
      |a j| ≤ (1 + Real.sqrt 2) ^ k * |∑ i ∈ Finset.Icc 1 k, a i * t ^ i| := by
  have hc : ContinuousOn (fun t : ℝ => |∑ i ∈ Finset.Icc 1 k, a i * t ^ i|) (Set.Icc (-1) 1) :=
    (by fun_prop : Continuous fun t : ℝ => |∑ i ∈ Finset.Icc 1 k, a i * t ^ i|).continuousOn
  obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (-1 : ℝ) ≤ 1)) hc
  refine ⟨t0, ht0, ?_⟩
  exact g59a_cauchy k a j hj hjk _ fun z hz => g59a_disk k a _ (fun t ht => hmax ht) z hz

theorem solution (k : ℕ) (a : ℕ → ℝ) (j : ℕ)
    (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1,
      |a j| ≤ (1 + Real.sqrt 2) ^ k * |∑ i ∈ Finset.Icc 1 k, a i * t ^ i| := g59a_poly k a j hj hjk

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P35.epr_lower_bound_monotone_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:08:10.738982+00:00
-- url     : https://prove2.me/submissions/85b7d698-7803-44c3-af9e-a58d9aca447b

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P35
noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsBarycenter tensorApply traceSize)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedRelativeEntropyNats binaryEntropyBits)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix coherentCoefficient)

open QAlgorithms.Papers.Independent.Support50.P20 (IsBinaryEffect)

attribute [local instance] Classical.propDecidable Classical.decEq


lemma p35s_glog_mono (x : ℝ) (hx : 0 ≤ x) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    s * Real.log (1 + x / s) ≤ t * Real.log (1 + x / t) := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hc := (strictConcaveOn_log_Ioi).concaveOn
  have h1 : (1:ℝ) ∈ Set.Ioi (0:ℝ) := by norm_num
  have h2 : (1 + x / s) ∈ Set.Ioi (0:ℝ) := by
    show 0 < 1 + x/s; positivity
  have ha : 0 ≤ 1 - s / t := by rw [sub_nonneg, div_le_one ht]; exact hst
  have hb : 0 ≤ s / t := by positivity
  have := hc.2 h1 h2 ha hb (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at this
  have heq : (1 - s / t) * 1 + s / t * (1 + x / s) = 1 + x / t := by
    field_simp; ring
  rw [heq] at this
  have := mul_le_mul_of_nonneg_left this ht.le
  calc s * Real.log (1 + x / s) = t * (s / t * Real.log (1 + x / s)) := by
        field_simp
    _ ≤ _ := this

lemma p35s_theta_eq (kappa0 n : ℝ) (hk : kappa0 ∈ Set.Ico (0 : ℝ) 1) (hn : 0 ≤ n) (s : ℕ) :
    thetaFinite kappa0 s n =
      Real.exp (-(2 * ((s:ℝ) * Real.log (1 + n * (1 - Real.sqrt kappa0) / s)))) / 2 := by
  unfold thetaFinite
  have hx : 0 ≤ n * (1 - Real.sqrt kappa0) := by
    apply mul_nonneg hn
    rw [sub_nonneg, Real.sqrt_le_one]; exact hk.2.le
  have hpos : 0 < 1 + n * (1 - Real.sqrt kappa0) / s := by positivity
  have : (1 + (n / s) * (1 - Real.sqrt kappa0)) = 1 + n * (1 - Real.sqrt kappa0) / s := by ring
  rw [this, ← Real.exp_log hpos, ← Real.exp_nat_mul, Real.exp_log hpos, Real.exp_neg]
  push_cast
  rw [show (2 * (s:ℝ)) * Real.log (1 + n * (1 - Real.sqrt kappa0) / s)
      = 2 * ((s:ℝ) * Real.log (1 + n * (1 - Real.sqrt kappa0) / s)) by ring]
  field_simp

lemma p35s_theta_anti (kappa0 n : ℝ) (hk : kappa0 ∈ Set.Ico (0 : ℝ) 1) (hn : 0 ≤ n) :
    Antitone (fun s : ℕ => thetaFinite kappa0 s n) := by
  have hx : 0 ≤ n * (1 - Real.sqrt kappa0) := by
    apply mul_nonneg hn
    rw [sub_nonneg, Real.sqrt_le_one]; exact hk.2.le
  intro s t hst
  simp only [p35s_theta_eq kappa0 n hk hn]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rcases Nat.eq_zero_or_pos s with h | h
  · subst h
    simp only [Nat.cast_zero, zero_mul]
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    have : 0 ≤ n * (1 - Real.sqrt kappa0) / t := by positivity
    linarith
  · exact p35s_glog_mono _ hx (by exact_mod_cast h) (by exact_mod_cast hst)

lemma p35s_theta_mem (kappa0 n : ℝ) (hk : kappa0 ∈ Set.Ico (0 : ℝ) 1) (hn : 0 ≤ n) (s : ℕ) :
    thetaFinite kappa0 s n ∈ Set.Icc (0:ℝ) 2⁻¹ := by
  have hx : 0 ≤ n * (1 - Real.sqrt kappa0) := by
    apply mul_nonneg hn
    rw [sub_nonneg, Real.sqrt_le_one]; exact hk.2.le
  rw [p35s_theta_eq kappa0 n hk hn]
  constructor
  · positivity
  · have : Real.exp (-(2 * ((s:ℝ) * Real.log (1 + n * (1 - Real.sqrt kappa0) / s)))) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]
      apply mul_nonneg (by norm_num)
      apply mul_nonneg (by positivity)
      apply Real.log_nonneg
      have : 0 ≤ n * (1 - Real.sqrt kappa0) / s := by positivity
      linarith
    linarith

lemma p35s_thetaLimit_mem (kappa0 n : ℝ) (hk : kappa0 ∈ Set.Ico (0 : ℝ) 1) (hn : 0 ≤ n) :
    thetaLimit kappa0 n ∈ Set.Icc (0:ℝ) 2⁻¹ := by
  have hx : 0 ≤ n * (1 - Real.sqrt kappa0) := by
    apply mul_nonneg hn
    rw [sub_nonneg, Real.sqrt_le_one]; exact hk.2.le
  unfold thetaLimit
  constructor
  · positivity
  · have : Real.exp (-2 * n * (1 - Real.sqrt kappa0)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    linarith

lemma p35s_bits (q : ℝ) : binaryEntropyBits q = Real.binEntropy q / Real.log 2 := by
  unfold binaryEntropyBits Real.binEntropy
  congr 1
  rw [Real.log_inv, Real.log_inv]; ring

lemma p35s_rate_mono (a b : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 2⁻¹) (hb : b ∈ Set.Icc (0:ℝ) 2⁻¹)
    (hab : b ≤ a) : 1 - binaryEntropyBits a ≤ 1 - binaryEntropyBits b := by
  rw [p35s_bits, p35s_bits]
  have := Real.binEntropy_strictMonoOn.monotoneOn hb ha hab
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have := div_le_div_of_nonneg_right this hl.le
  linarith

lemma p35s_theta_tendsto (kappa0 n : ℝ) :
    Tendsto (fun s : ℕ => thetaFinite kappa0 s n) atTop (𝓝 (thetaLimit kappa0 n)) := by
  set x := n * (1 - Real.sqrt kappa0)
  have h1 := Real.tendsto_one_add_div_pow_exp x
  have h2 : Tendsto (fun s : ℕ => 1 / (2 * ((1 + x / s) ^ s) ^ 2)) atTop
      (𝓝 (1 / (2 * (Real.exp x) ^ 2))) := by
    apply Tendsto.div tendsto_const_nhds
    · exact (h1.pow 2).const_mul 2
    · positivity
  have he : 1 / (2 * (Real.exp x) ^ 2) = thetaLimit kappa0 n := by
    unfold thetaLimit
    rw [← Real.exp_nat_mul, show -2 * n * (1 - Real.sqrt kappa0) = -((2:ℕ) * x) by
      simp [x]; ring, Real.exp_neg]
    field_simp
  rw [he] at h2
  refine h2.congr (fun s => ?_)
  unfold thetaFinite
  rw [← pow_mul, mul_comm s 2]
  congr 3
  simp [x]; ring

end QAlgorithms.Papers.Independent.Advance50.P35

open QAlgorithms.Papers.Independent.Advance50.P35
open QAlgorithms.Papers.Independent.Frontier18.P07 (binaryEntropyBits)

theorem solution (kappa0 n : ℝ)
    (hk : kappa0 ∈ Set.Ico (0 : ℝ) 1) (hn : 0 ≤ n) :
    (∀ s t : ℕ, 1 ≤ s → s ≤ t → eprLowerRate kappa0 s n ≤ eprLowerRate kappa0 t n) ∧
      Tendsto (fun s : ℕ => thetaFinite kappa0 s n) atTop (𝓝 (thetaLimit kappa0 n)) ∧
      Tendsto (fun s : ℕ => eprLowerRate kappa0 s n) atTop (𝓝 (eprLimitRate kappa0 n)) ∧
      ∀ s : ℕ, 1 ≤ s →
        eprLowerRate kappa0 1 n ≤ eprLowerRate kappa0 s n ∧
        eprLowerRate kappa0 s n ≤ eprLimitRate kappa0 n := by
  have hanti := p35s_theta_anti kappa0 n hk hn
  have hmem := p35s_theta_mem kappa0 n hk hn
  have hmono : Monotone (fun s : ℕ => eprLowerRate kappa0 s n) := fun s t hst =>
    p35s_rate_mono _ _ (hmem s) (hmem t) (hanti hst)
  have hth := p35s_theta_tendsto kappa0 n
  have hrate : Tendsto (fun s : ℕ => eprLowerRate kappa0 s n) atTop (𝓝 (eprLimitRate kappa0 n)) := by
    unfold eprLowerRate eprLimitRate
    simp only [p35s_bits]
    apply Tendsto.const_sub
    apply Tendsto.div_const
    exact (Real.binEntropy_continuous.tendsto _).comp hth
  refine ⟨fun s t _ hst => hmono hst, hth, hrate, fun s hs => ⟨hmono hs, hmono.ge_of_tendsto hrate s⟩⟩

end

-- Prove2me | solution 1 for PrivateContinualCounting.Kraft.lti_divergence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:45:04.868437+00:00
-- url     : https://prove2.me/submissions/ecd33f11-709a-412d-8d5a-0ed9bcdf486f

import Theorems.Thm_PrivateContinualCounting_Kraft_hilbert_log_divergence
import Theorems.Thm_PrivateContinualCounting_Kraft_fixed_period
import Definitions.Def_PrivateContinualCounting_Kraft_LTIFactors
import Definitions.Def_PrivateContinualCounting_Kraft_PeriodicCounter

set_option autoImplicit false

open Finset Filter Topology

namespace PCCKraftNec
open PrivateContinualCounting.Kraft

lemma vectorSq_nonneg {m : ℕ} (x : Fin m → ℝ) : 0 ≤ vectorSq x :=
  sum_nonneg (fun q _ => sq_nonneg _)

lemma abs_dot_le {m : ℕ} (x y : Fin m → ℝ) :
    |∑ q, x q * y q| ≤ Real.sqrt (vectorSq x) * Real.sqrt (vectorSq y) := by
  have hcs := sum_mul_sq_le_sq_mul_sq univ x y
  have hx : vectorSq x = ∑ q, x q ^ 2 := by simp [vectorSq, Real.norm_eq_abs, sq_abs]
  have hy : vectorSq y = ∑ q, y q ^ 2 := by simp [vectorSq, Real.norm_eq_abs, sq_abs]
  rw [hx, hy, ← Real.sqrt_mul (sum_nonneg (fun q _ => sq_nonneg _))]
  exact Real.abs_le_sqrt hcs

/-- The norm data of real vector LTI factors satisfy the hypotheses of the core lemmas. -/
lemma lti_norms {m : ℕ} (d : LTIData ℝ m) (hd : IsLTI d) :
    (∀ j, 0 ≤ Real.sqrt (vectorSq (d.l j))) ∧ (∀ k, 0 ≤ Real.sqrt (vectorSq (d.r k))) ∧
    Summable (fun k => Real.sqrt (vectorSq (d.r k)) ^ 2) ∧
    (∀ s, 1 ≤ ∑ j ∈ range (s + 1),
      Real.sqrt (vectorSq (d.l j)) * Real.sqrt (vectorSq (d.r (s - j)))) ∧
    (∀ t, ∑ j ∈ range t, Real.sqrt (vectorSq (d.l j)) ^ 2 = d.energy t) ∧
    (∀ k, Real.sqrt (vectorSq (d.r k)) ^ 2 = vectorSq (d.r k)) := by
  obtain ⟨_, hconv, hsum⟩ := hd
  have hsq : ∀ x : Fin m → ℝ, Real.sqrt (vectorSq x) ^ 2 = vectorSq x :=
    fun x => Real.sq_sqrt (vectorSq_nonneg x)
  refine ⟨fun j => Real.sqrt_nonneg _, fun k => Real.sqrt_nonneg _, ?_, ?_, ?_, fun k => hsq _⟩
  · simpa [hsq] using hsum
  · intro s
    calc (1:ℝ) = ∑ j ∈ range (s + 1), ∑ q, d.l j q * d.r (s - j) q := (hconv s).symm
      _ ≤ ∑ j ∈ range (s + 1), |∑ q, d.l j q * d.r (s - j) q| :=
          sum_le_sum (fun j _ => le_abs_self _)
      _ ≤ _ := sum_le_sum (fun j _ => abs_dot_le _ _)
  · intro t; simp [LTIData.energy, hsq]

lemma deltaSq_pos {m : ℕ} (d : LTIData ℝ m) (hd : IsLTI d) : 0 < d.deltaSq := by
  obtain ⟨hα, hβ, hβ2, hid, _, hsq⟩ := lti_norms d hd
  have h0 := hid 0
  simp only [zero_add, sum_range_one, Nat.sub_zero] at h0
  have hb : 0 < Real.sqrt (vectorSq (d.r 0)) := by
    by_contra h
    have : Real.sqrt (vectorSq (d.r 0)) = 0 := le_antisymm (not_lt.mp h) (hβ 0)
    rw [this, mul_zero] at h0
    linarith
  have hv : 0 < vectorSq (d.r 0) := by rw [← hsq]; positivity
  have hsum : Summable (fun k => vectorSq (d.r k)) := by simpa [hsq] using hβ2
  exact lt_of_lt_of_le hv (hsum.le_tsum 0 (fun k _ => vectorSq_nonneg _))

/-- Theorem 3.1 for real vector LTI factors: energy and variance. -/
theorem lti_energy_diverges {m : ℕ} (d : LTIData ℝ m) (hd : IsLTI d) :
    LogSqDiverges d.energy := by
  obtain ⟨hα, hβ, hβ2, hid, hE, _⟩ := lti_norms d hd
  have := hilbert_log_divergence _ _ hα hβ hβ2 hid
  unfold LogSqDiverges
  simpa [hE] using this

theorem lti_variance_diverges {m : ℕ} (d : LTIData ℝ m) (hd : IsLTI d) :
    LogSqDiverges d.variance := by
  have h := (lti_energy_diverges d hd).const_mul_atTop (deltaSq_pos d hd)
  unfold LogSqDiverges
  refine h.congr (fun t => ?_)
  simp [LTIData.variance, mul_div_assoc]

section
variable {m : ℕ} (d : LTIData ℂ m)

lemma realify_l_sq (j : ℕ) : vectorSq ((realify d).l j) = vectorSq (d.l j) := by
  simp only [vectorSq, realify]
  rw [Fin.sum_univ_add]
  simp only [Fin.coe_castAdd, Fin.is_lt, dite_true, Fin.coe_natAdd, add_lt_iff_neg_left,
    not_lt_zero', dite_false, add_tsub_cancel_left, Fin.eta, Real.norm_eq_abs, sq_abs, neg_sq]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  rw [← Complex.sq_norm_sub_sq_re]
  ring

lemma realify_r_sq (k : ℕ) : vectorSq ((realify d).r k) = vectorSq (d.r k) := by
  simp only [vectorSq, realify]
  rw [Fin.sum_univ_add]
  simp only [Fin.coe_castAdd, Fin.is_lt, dite_true, Fin.coe_natAdd, add_lt_iff_neg_left,
    not_lt_zero', dite_false, add_tsub_cancel_left, Fin.eta, Real.norm_eq_abs, sq_abs]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  rw [← Complex.sq_norm_sub_sq_re]
  ring

lemma realify_dot (j k : ℕ) :
    ∑ q, (realify d).l j q * (realify d).r k q = (∑ q, d.l j q * d.r k q).re := by
  simp only [realify]
  rw [Fin.sum_univ_add, Complex.re_sum]
  simp only [Fin.coe_castAdd, Fin.is_lt, dite_true, Fin.coe_natAdd, add_lt_iff_neg_left,
    not_lt_zero', dite_false, add_tsub_cancel_left, Fin.eta, Complex.mul_re]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  ring

lemma realify_isLTI (hd : IsLTI d) : IsLTI (realify d) := by
  obtain ⟨hm, hconv, hsum⟩ := hd
  refine ⟨by omega, fun s => ?_, ?_⟩
  · simp_rw [realify_dot]
    rw [← Complex.re_sum, hconv s, Complex.one_re]
  · simpa [realify_r_sq] using hsum

lemma realify_energy (t : ℕ) : (realify d).energy t = d.energy t := by
  simp [LTIData.energy, realify_l_sq]

lemma realify_deltaSq : (realify d).deltaSq = d.deltaSq := by
  simp [LTIData.deltaSq, realify_r_sq]

lemma realify_variance (t : ℕ) : (realify d).variance t = d.variance t := by
  simp [LTIData.variance, realify_energy, realify_deltaSq]

end

end PCCKraftNec

namespace PCCKraftPer
open PrivateContinualCounting.Kraft

lemma l2_summable {I : Type} (f : I → ℝ) (h : Memℓp f 2) : Summable (fun i => f i ^ 2) := by
  have := (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).1 h
  simpa [Real.norm_eq_abs, sq_abs] using this

lemma summable_mul_of_sq {I : Type} (x y : I → ℝ) (hx : Summable (fun i => x i ^ 2))
    (hy : Summable (fun i => y i ^ 2)) : Summable (fun i => x i * y i) := by
  refine Summable.of_norm_bounded (hx.add hy) (fun i => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|x i| - |y i|), sq_abs (x i), sq_abs (y i)]

lemma tsum_cs {I : Type} (x y : I → ℝ) (hx : Summable (fun i => x i ^ 2))
    (hy : Summable (fun i => y i ^ 2)) :
    |∑' i, x i * y i| ≤ Real.sqrt (∑' i, x i ^ 2) * Real.sqrt (∑' i, y i ^ 2) := by
  have hxa : Summable (fun i => |x i| ^ (2:ℝ)) := by simpa [Real.rpow_two, sq_abs] using hx
  have hya : Summable (fun i => |y i| ^ (2:ℝ)) := by simpa [Real.rpow_two, sq_abs] using hy
  have hH := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (fun i => abs_nonneg (x i)) (fun i => abs_nonneg (y i)) hxa hya
  have hxy := summable_mul_of_sq x y hx hy
  have h1 : |∑' i, x i * y i| ≤ ∑' i, |x i| * |y i| := by
    have := norm_tsum_le_tsum_norm hxy.norm
    simpa [Real.norm_eq_abs, abs_mul] using this
  refine h1.trans (le_of_eq_of_le ?_ hH |>.trans (le_of_eq ?_))
  · rfl
  · simp only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow]

section
variable {p : ℕ} {I₀ : Type} [Countable I₀] (M : PeriodicCounter p I₀)

lemma R_col0 (b' : ℕ) (i : I₀) :
    M.counter.factors.R (b', i) 0 = M.Rblock b' i ⟨0, M.positive_period⟩ := by
  have := M.strategy_toeplitz b' i 0 ⟨0, M.positive_period⟩
  simpa using this

lemma L_fiber_summable (j : ℕ) (a : Fin p) : Summable (fun i => M.Lblock j a i ^ 2) := by
  have h := l2_summable _ (M.counter.factors.rows_l2 (p * j + a.val))
  have h2 := h.comp_injective (i := fun i : I₀ => ((0:ℕ), i)) (fun i i' hii => by simpa using hii)
  refine h2.congr (fun i => ?_)
  show M.counter.factors.L (p * j + a.val) (0, i) ^ 2 = M.Lblock j a i ^ 2
  rw [M.decoder_toeplitz]
  simp

lemma R_col0_summable :
    Summable (fun x : ℕ × I₀ => M.Rblock x.1 x.2 ⟨0, M.positive_period⟩ ^ 2) := by
  have h := l2_summable _ (M.counter.factors.cols_l2 0)
  refine h.congr (fun x => ?_)
  obtain ⟨b', i⟩ := x
  rw [R_col0]

/-- The column energy `Σ_k ‖r_k‖²` of input phase `0`. -/
noncomputable def beta (k : ℕ) : ℝ :=
  Real.sqrt (∑' i, M.Rblock k i ⟨0, M.positive_period⟩ ^ 2)

noncomputable def alpha (a : Fin p) (j : ℕ) : ℝ := Real.sqrt (∑' i, M.Lblock j a i ^ 2)

lemma beta_sq (k : ℕ) : beta M k ^ 2 = ∑' i, M.Rblock k i ⟨0, M.positive_period⟩ ^ 2 :=
  Real.sq_sqrt (tsum_nonneg (fun i => sq_nonneg _))

lemma alpha_sq (a : Fin p) (j : ℕ) : alpha M a j ^ 2 = ∑' i, M.Lblock j a i ^ 2 :=
  Real.sq_sqrt (tsum_nonneg (fun i => sq_nonneg _))

lemma beta_sq_summable : Summable (fun k => beta M k ^ 2) := by
  simp_rw [beta_sq]
  exact (R_col0_summable M).prod

lemma beta_sq_tsum : ∑' k, beta M k ^ 2 =
    ∑' x : ℕ × I₀, M.Rblock x.1 x.2 ⟨0, M.positive_period⟩ ^ 2 := by
  simp_rw [beta_sq]
  exact ((R_col0_summable M).tsum_prod).symm

lemma conv_identity (a : Fin p) (m : ℕ) :
    ∑ j ∈ range (m + 1), ∑' i, M.Lblock j a i * M.Rblock (m - j) i ⟨0, M.positive_period⟩ = 1 := by
  set z : Fin p := ⟨0, M.positive_period⟩
  have hprod := M.counter.factors.product (p * m + a.val) 0
  rw [if_pos (Nat.zero_le _)] at hprod
  set f : ℕ × I₀ → ℝ := fun x => M.counter.factors.L (p * m + a.val) x *
    M.counter.factors.R x 0 with hf
  have hfs : Summable f :=
    summable_mul_of_sq _ _ (l2_summable _ (M.counter.factors.rows_l2 _))
      (l2_summable _ (M.counter.factors.cols_l2 0))
  have hf' : ∀ b' i, f (b', i) = (if b' ≤ m then M.Lblock (m - b') a i else 0) * M.Rblock b' i z := by
    intro b' i
    rw [hf]
    dsimp only
    rw [M.decoder_toeplitz, R_col0]
  rw [hfs.tsum_prod] at hprod
  have hzero : ∀ b' ∉ range (m + 1), ∑' i, f (b', i) = 0 := by
    intro b' hb
    have : ¬ b' ≤ m := by simpa [Nat.lt_succ_iff] using hb
    simp [hf', this]
  rw [tsum_eq_sum hzero] at hprod
  rw [← hprod, ← sum_range_reflect]
  apply sum_congr rfl
  intro j hj
  have hj' : j < m + 1 := mem_range.mp hj
  apply tsum_congr
  intro i
  rw [hf']
  have h1 : j ≤ m := by omega
  rw [if_pos h1]
  have h3 : m + 1 - 1 - j = m - j := by omega
  have h2 : m - (m - j) = j := by omega
  rw [h3, h2]

lemma alpha_beta_identity (a : Fin p) (m : ℕ) :
    1 ≤ ∑ j ∈ range (m + 1), alpha M a j * beta M (m - j) := by
  rw [← conv_identity M a m]
  apply sum_le_sum
  intro j _
  refine (le_abs_self _).trans ?_
  have := tsum_cs (fun i => M.Lblock j a i) (fun i => M.Rblock (m - j) i ⟨0, M.positive_period⟩)
    (L_fiber_summable M j a) ((R_col0_summable M).prod_factor (m - j))
  simpa [alpha, beta] using this

theorem phase_diverges (a : Fin p) : LogSqDiverges (M.phaseEnergy a) := by
  have h := hilbert_log_divergence (alpha M a) (beta M) (fun j => Real.sqrt_nonneg _)
    (fun k => Real.sqrt_nonneg _) (beta_sq_summable M) (alpha_beta_identity M a)
  unfold LogSqDiverges
  refine h.congr (fun n => ?_)
  simp [PeriodicCounter.phaseEnergy, alpha_sq]


end

end PCCKraftPer

open PrivateContinualCounting.Kraft in
theorem solution :
    (∀ (m : ℕ) (d : LTIData ℝ m), IsLTI d →
      LogSqDiverges d.energy ∧ LogSqDiverges d.variance) ∧
    (∀ (m : ℕ) (d : LTIData ℂ m), IsLTI d →
      LogSqDiverges d.energy ∧ LogSqDiverges d.variance ∧
      IsLTI (realify d) ∧ (∀ t, (realify d).energy t = d.energy t) ∧
      (realify d).deltaSq = d.deltaSq) ∧
    (∀ (p : ℕ) (I₀ : Type) [Countable I₀] (M : PeriodicCounter p I₀),
      (∀ a : Fin p, LogSqDiverges (M.phaseEnergy a)) ∧
      LogSqDiverges M.counter.variance) := by
  refine ⟨fun m d hd => ⟨PCCKraftNec.lti_energy_diverges d hd,
    PCCKraftNec.lti_variance_diverges d hd⟩, fun m d hd => ?_,
    fun p I₀ _ M => ⟨PCCKraftPer.phase_diverges M, fixed_period p I₀ M⟩⟩
  have hr := PCCKraftNec.realify_isLTI d hd
  have h1 := PCCKraftNec.lti_energy_diverges _ hr
  have h2 := PCCKraftNec.lti_variance_diverges _ hr
  refine ⟨?_, ?_, hr, PCCKraftNec.realify_energy d, PCCKraftNec.realify_deltaSq d⟩
  · simpa [LogSqDiverges, PCCKraftNec.realify_energy] using h1
  · simpa [LogSqDiverges, PCCKraftNec.realify_variance] using h2

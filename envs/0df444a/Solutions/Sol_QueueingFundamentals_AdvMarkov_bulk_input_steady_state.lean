-- Prove2me | solution 1 for QueueingFundamentals.AdvMarkov.bulk_input_steady_state
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:44:18.339138+00:00
-- url     : https://prove2.me/submissions/47a472ef-0905-4945-950e-54534cdadc0e

import Mathlib
import Definitions.Def_QueueingFundamentals_AdvMarkov_BulkInput

open Filter Topology Finset

namespace QueueingFundamentals.AdvMarkov

noncomputable def bkT (c : ℕ → ℝ) (m : ℕ) : ℝ := 1 - ∑ k ∈ range (m + 1), c k

noncomputable def bkConv (p c : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ range (n + 1), p j * c (n - j)

lemma bk_sum_Icc_one (g : ℕ → ℝ) (n : ℕ) : ∑ k ∈ Icc 1 n, g k = ∑ i ∈ range n, g (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

lemma bk_bal_sum (p c : ℕ → ℝ) (hc0 : c 0 = 0) (n : ℕ) :
    ∑ k ∈ Icc 1 n, p (n - k) * c k = bkConv p c n := by
  unfold bkConv
  rw [← sum_range_reflect, sum_range_succ', bk_sum_Icc_one]
  rw [show n - (n + 1 - 1 - 0) = 0 by omega, hc0, mul_zero, add_zero]
  refine sum_congr rfl (fun i hi => ?_)
  simp at hi
  rw [show n + 1 - 1 - (i + 1) = n - (i + 1) by omega, show n - (n - (i + 1)) = i + 1 by omega]

lemma bkT_zero (c : ℕ → ℝ) (hc0 : c 0 = 0) : bkT c 0 = 1 := by simp [bkT, hc0]

lemma bkT_succ (c : ℕ → ℝ) (m : ℕ) : bkT c (m + 1) = bkT c m - c (m + 1) := by
  unfold bkT; rw [sum_range_succ (n := m + 1)]; ring

lemma bk_D (p c : ℕ → ℝ) (hc0 : c 0 = 0) (m : ℕ) :
    ∑ j ∈ range (m + 2), p j * bkT c (m + 1 - j) =
      ∑ j ∈ range (m + 1), p j * bkT c (m - j) + p (m + 1) - bkConv p c (m + 1) := by
  unfold bkConv
  rw [sum_range_succ, sum_range_succ (n := m + 1)]
  simp only [Nat.sub_self, bkT_zero c hc0, hc0, mul_one, mul_zero, add_zero]
  have : ∀ j ∈ range (m + 1), p j * bkT c (m + 1 - j) = p j * bkT c (m - j) - p j * c (m + 1 - j) := by
    intro j hj
    simp at hj
    rw [show m + 1 - j = (m - j) + 1 by omega, bkT_succ]; ring
  rw [sum_congr rfl this, sum_sub_distrib]
  ring

lemma bk_cut (lam mu : ℝ) (c p : ℕ → ℝ) (hc0 : c 0 = 0) (hb : BulkInputBalance lam mu c p) :
    ∀ n, mu * p (n + 1) = lam * ∑ j ∈ range (n + 1), p j * bkT c (n - j) := by
  intro n
  induction n with
  | zero =>
    simp [bkT_zero c hc0]
    linarith [hb.2]
  | succ n ih =>
    have h1 := hb.1 (n + 1) (by omega)
    rw [bk_bal_sum p c hc0] at h1
    rw [show n + 1 + 1 = n + 2 by ring] at h1 ⊢
    rw [bk_D p c hc0 n]
    linear_combination ih - h1

lemma bk_cut_bal (lam mu : ℝ) (c p : ℕ → ℝ) (hc0 : c 0 = 0)
    (hcut : ∀ n, mu * p (n + 1) = lam * ∑ j ∈ range (n + 1), p j * bkT c (n - j)) :
    BulkInputBalance lam mu c p := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [bk_bal_sum p c hc0]
    have h1 := hcut (m + 1)
    have h2 := hcut m
    rw [show m + 1 + 1 = m + 2 by ring, bk_D p c hc0 m] at h1
    linear_combination h2 - h1
  · have := hcut 0
    simp [bkT_zero c hc0] at this
    linarith


lemma bkT_hasSum (c : ℕ → ℝ) (hc : IsBatchSizeDist c) (m : ℕ) :
    HasSum (fun i => c (i + (m + 1))) (bkT c m) :=
  (hasSum_nat_add_iff' (m + 1)).mpr hc.2.2

lemma bkT_nonneg (c : ℕ → ℝ) (hc : IsBatchSizeDist c) (m : ℕ) : 0 ≤ bkT c m :=
  hasSum_le (fun i => hc.2.1 _) hasSum_zero (bkT_hasSum c hc m)

lemma bk_tail_weighted (c : ℕ → ℝ) (hc : IsBatchSizeDist c) (w : ℕ → ℝ) (hw : ∀ m, 0 ≤ w m)
    (hW : Summable (fun k => (∑ m ∈ range k, w m) * c k)) :
    HasSum (fun m => w m * bkT c m) (∑' k, (∑ m ∈ range k, w m) * c k) := by
  set W : ℕ → ℝ := fun k => ∑ m ∈ range k, w m with hWdef
  set f : ℕ → ℝ := fun k => W k * c k with hf
  have hI : ∀ N, ∑ m ∈ range N, w m * bkT c m = ∑ k ∈ range (N + 1), f k + W N * bkT c N := by
    intro N
    induction N with
    | zero => simp [hf, hWdef]
    | succ N ih =>
      rw [sum_range_succ, ih, sum_range_succ (n := N + 1), bkT_succ]
      simp only [hf, hWdef, sum_range_succ (n := N)]
      ring
  have hWmono : ∀ N k, N ≤ k → W N ≤ W k := fun N k h =>
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr h) (fun i _ _ => hw i)
  have hW0 : ∀ N, 0 ≤ W N := fun N => sum_nonneg (fun i _ => hw i)
  have htail : Tendsto (fun N => W N * bkT c N) atTop (𝓝 0) := by
    have hg := (tendsto_sum_nat_add f).comp (tendsto_add_atTop_nat 1)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg
      (fun N => mul_nonneg (hW0 N) (bkT_nonneg c hc N)) (fun N => ?_)
    simp only [Function.comp]
    have h1 := (bkT_hasSum c hc N).mul_left (W N)
    have h2 := ((summable_nat_add_iff (N + 1)).mpr hW).hasSum
    refine hasSum_le (fun i => ?_) h1 h2
    simp only [hf]
    exact mul_le_mul_of_nonneg_right (hWmono N _ (by omega)) (hc.2.1 _)
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun m => mul_nonneg (hw m) (bkT_nonneg c hc m))]
  have hS := (hW.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have := hS.add htail
  rw [add_zero] at this
  refine this.congr (fun N => ?_)
  simp only [Function.comp]
  rw [hI N]


lemma bk_conv_partial (a b : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, ∑ j ∈ range (n + 1), a j * b (n - j) =
      ∑ j ∈ range N, a j * ∑ m ∈ range (N - j), b m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ (n := N) (f := fun j => a j * ∑ m ∈ range (N + 1 - j), b m)]
    have : ∀ j ∈ range N, a j * ∑ m ∈ range (N + 1 - j), b m =
        a j * ∑ m ∈ range (N - j), b m + a j * b (N - j) := by
      intro j hj
      simp at hj
      rw [show N + 1 - j = (N - j) + 1 by omega, sum_range_succ]; ring
    rw [sum_congr rfl this, sum_add_distrib, sum_range_succ (n := N) (f := fun j => a j * b (N - j))]
    simp
    ring

lemma bk_conv_le (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (B : ℝ)
    (hB : ∀ M, ∑ m ∈ range M, b m ≤ B) (N : ℕ) :
    ∑ n ∈ range N, ∑ j ∈ range (n + 1), a j * b (n - j) ≤ (∑ j ∈ range N, a j) * B := by
  rw [bk_conv_partial, sum_mul]
  exact sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hB _) (ha j))

lemma bkT_hasSum_EX (c : ℕ → ℝ) (hc : IsBatchSizeDist c) (hc1 : Summable (fun n : ℕ => (n : ℝ) * c n)) :
    HasSum (bkT c) (∑' n : ℕ, (n : ℝ) * c n) := by
  have := bk_tail_weighted c hc (fun _ => 1) (fun _ => zero_le_one) (by simpa using hc1)
  simpa using this

lemma bk_shift_hasSum (lam mu : ℝ) (c p : ℕ → ℝ) (hc : IsBatchSizeDist c)
    (hc1 : Summable (fun n : ℕ => (n : ℝ) * c n)) (hnn : ∀ n, 0 ≤ p n) (hps : Summable p)
    (hcut : ∀ n, mu * p (n + 1) = lam * ∑ j ∈ range (n + 1), p j * bkT c (n - j)) (hmu : 0 < mu) :
    HasSum (fun n => p (n + 1)) (lam / mu * ((∑' n, p n) * ∑' n : ℕ, (n : ℝ) * c n)) := by
  have hT := bkT_hasSum_EX c hc hc1
  have h1 : Summable (fun n => ‖p n‖) := hps.congr (fun n => (Real.norm_of_nonneg (hnn n)).symm)
  have h2 : Summable (fun n => ‖bkT c n‖) :=
    hT.summable.congr (fun n => (Real.norm_of_nonneg (bkT_nonneg c hc n)).symm)
  have := (hasSum_sum_range_mul_of_summable_norm h1 h2).mul_left (lam / mu)
  rw [hT.tsum_eq] at this
  refine this.congr_fun (fun n => ?_)
  have := hcut n
  field_simp
  linarith

noncomputable def bkSeq (a p0 : ℝ) (T : ℕ → ℝ) : ℕ → ℝ
  | 0 => p0
  | n + 1 => a * ∑ j : Fin (n + 1), bkSeq a p0 T j * T (n - j)

lemma bkSeq_succ (a p0 : ℝ) (T : ℕ → ℝ) (n : ℕ) :
    bkSeq a p0 T (n + 1) = a * ∑ j ∈ range (n + 1), bkSeq a p0 T j * T (n - j) := by
  rw [bkSeq, Fin.sum_univ_eq_sum_range (fun j => bkSeq a p0 T j * T (n - j))]

lemma bk_exists (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (c : ℕ → ℝ) (hc : IsBatchSizeDist c) (hc1 : Summable (fun n : ℕ => (n : ℝ) * c n))
    (ρ : ℝ) (hρ : ρ = lam * (∑' n : ℕ, (n : ℝ) * c n) / mu) (hρ1 : ρ < 1) :
    ∃ p : ℕ → ℝ, IsBulkInputSteadyState lam mu c p := by
  set EX := ∑' n : ℕ, (n : ℝ) * c n with hEX
  have hT := bkT_hasSum_EX c hc hc1
  have hEX0 : 0 ≤ EX := hasSum_le (fun i => bkT_nonneg c hc i) hasSum_zero hT
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  set p := bkSeq (lam / mu) (1 - ρ) (bkT c) with hpdef
  have hnn : ∀ n, 0 ≤ p n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | n
      · simp [hpdef, bkSeq]; linarith
      · rw [hpdef, bkSeq_succ]
        apply mul_nonneg (by positivity)
        exact sum_nonneg (fun j hj => mul_nonneg (ih j (by simp at hj; omega)) (bkT_nonneg c hc _))
  have hcut : ∀ n, mu * p (n + 1) = lam * ∑ j ∈ range (n + 1), p j * bkT c (n - j) := by
    intro n
    rw [hpdef, bkSeq_succ]
    field_simp
  have hp0 : p 0 = 1 - ρ := by simp [hpdef, bkSeq]
  have hTB : ∀ M, ∑ m ∈ range M, bkT c m ≤ EX :=
    fun M => sum_le_hasSum (range M) (fun i _ => bkT_nonneg c hc i) hT
  have hbound : ∀ N, ∑ n ∈ range N, p n ≤ 1 := by
    intro N
    rcases N with _ | N
    · simp
    have e1 : ∑ n ∈ range (N + 1), p n = p 0 + ∑ n ∈ range N, p (n + 1) := by
      rw [sum_range_succ']; ring
    have e2 : ∑ n ∈ range N, p (n + 1) =
        lam / mu * ∑ n ∈ range N, ∑ j ∈ range (n + 1), p j * bkT c (n - j) := by
      rw [mul_sum]
      refine sum_congr rfl (fun n _ => ?_)
      have := hcut n
      field_simp
      linarith
    have e3 := bk_conv_le p (bkT c) hnn EX hTB N
    have e4 : ∑ j ∈ range N, p j ≤ ∑ n ∈ range (N + 1), p n := by
      rw [sum_range_succ]; linarith [hnn N]
    have hρ' : lam / mu * EX = ρ := by rw [hρ]; ring
    have : ∑ n ∈ range (N + 1), p n ≤ (1 - ρ) + ρ * ∑ n ∈ range (N + 1), p n := by
      have e0 : ∑ n ∈ range (N + 1), p n = (1 - ρ) +
          lam / mu * ∑ n ∈ range N, ∑ j ∈ range (n + 1), p j * bkT c (n - j) := by
        rw [e1, e2, hp0]
      rw [e0]
      rw [← e0]
      have h5 : lam / mu * ∑ n ∈ range N, ∑ j ∈ range (n + 1), p j * bkT c (n - j) ≤
          lam / mu * ((∑ j ∈ range N, p j) * EX) :=
        mul_le_mul_of_nonneg_left e3 (by positivity)
      have h6 : lam / mu * ((∑ j ∈ range N, p j) * EX) = ρ * ∑ j ∈ range N, p j := by
        rw [← hρ']; ring
      have h7 : ρ * ∑ j ∈ range N, p j ≤ ρ * ∑ n ∈ range (N + 1), p n :=
        mul_le_mul_of_nonneg_left e4 hρ0
      linarith
    nlinarith
  have hps : Summable p := summable_of_sum_range_le hnn hbound
  have hsh := bk_shift_hasSum lam mu c p hc hc1 hnn hps hcut hmu
  have hsh2 := (hasSum_nat_add_iff' 1).mpr hps.hasSum
  simp only [range_one, sum_singleton] at hsh2
  have hu := hsh.unique hsh2
  have hS : ∑' n, p n = 1 := by
    rw [hp0] at hu
    have hρ' : lam / mu * ((∑' n, p n) * EX) = ρ * ∑' n, p n := by rw [hρ]; ring
    rw [hρ'] at hu
    have : (1 - ρ) * (∑' n, p n - 1) = 0 := by linarith
    have h1 : (1 - ρ) ≠ 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left h1
    linarith
  refine ⟨p, hnn, ?_, bk_cut_bal lam mu c p hc.1 hcut⟩
  rw [← hS]; exact hps.hasSum


lemma bk_norm_one_sub_pow (z : ℂ) (hz : ‖z‖ ≤ 1) (n : ℕ) : ‖1 - z ^ n‖ ≤ n * ‖1 - z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : 1 - z ^ (n + 1) = (1 - z ^ n) + z ^ n * (1 - z) := by ring
    rw [e]
    calc ‖(1 - z ^ n) + z ^ n * (1 - z)‖ ≤ ‖1 - z ^ n‖ + ‖z ^ n * (1 - z)‖ := norm_add_le _ _
      _ ≤ n * ‖1 - z‖ + 1 * ‖1 - z‖ := by
          gcongr
          rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hz) (norm_nonneg _)
      _ = ((n + 1 : ℕ) : ℝ) * ‖1 - z‖ := by push_cast; ring

lemma bk_cpgf_summ (p : ℕ → ℝ) (hnn : ∀ n, 0 ≤ p n) (hps : Summable p) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Summable (fun n => ‖(p n : ℂ) * z ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hps
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hnn n)]
  exact mul_le_of_le_one_right (hnn n) (pow_le_one₀ (norm_nonneg _) hz)

lemma bk_pgf (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (c : ℕ → ℝ) (hc : IsBatchSizeDist c) (hc1 : Summable (fun n : ℕ => (n : ℝ) * c n))
    (hst : lam * (∑' n : ℕ, (n : ℝ) * c n) < mu)
    (p : ℕ → ℝ) (hp : IsBulkInputSteadyState lam mu c p) (z : ℂ) (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    cpgf p z = (mu : ℂ) * (p 0 : ℂ) * (1 - z) /
      ((mu : ℂ) * (1 - z) - (lam : ℂ) * z * (1 - cpgf c z)) := by
  set EX := ∑' n : ℕ, (n : ℝ) * c n with hEX
  have hps : Summable p := hp.2.1.summable
  have hcs : Summable c := hc.2.2.summable
  have sa := bk_cpgf_summ p hp.1 hps z hz
  have sb := bk_cpgf_summ c hc.2.1 hcs z hz
  set P := cpgf p z with hP
  set C := cpgf c z with hC
  -- denominator
  have h1z : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have hCb : ‖1 - C‖ ≤ EX * ‖1 - z‖ := by
    have hc1' : HasSum (fun n => ((c n : ℝ) : ℂ)) 1 := by
      have := Complex.hasSum_ofReal.mpr hc.2.2; simpa using this
    have h2 : HasSum (fun n => (c n : ℂ) * (1 - z ^ n)) (1 - C) := by
      have := hc1'.sub (sb.of_norm.hasSum)
      refine this.congr_fun (fun n => ?_)
      ring
    have hg : HasSum (fun n : ℕ => (n : ℝ) * c n * ‖1 - z‖) (EX * ‖1 - z‖) :=
      hc1.hasSum.mul_right _
    rw [← h2.tsum_eq]
    refine tsum_of_norm_bounded hg (fun n => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc.2.1 n)]
    calc c n * ‖1 - z ^ n‖ ≤ c n * (n * ‖1 - z‖) :=
          mul_le_mul_of_nonneg_left (bk_norm_one_sub_pow z hz n) (hc.2.1 n)
      _ = n * c n * ‖1 - z‖ := by ring
  have hden : (mu : ℂ) * (1 - z) - (lam : ℂ) * z * (1 - C) ≠ 0 := by
    intro h
    have e : (mu : ℂ) * (1 - z) = (lam : ℂ) * z * (1 - C) := by linear_combination h
    have e2 := congrArg norm e
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hmu.le,
      Real.norm_of_nonneg hlam.le] at e2
    have : lam * ‖z‖ * ‖1 - C‖ ≤ lam * EX * ‖1 - z‖ := by
      calc lam * ‖z‖ * ‖1 - C‖ ≤ lam * 1 * ‖1 - C‖ := by gcongr
        _ ≤ lam * (EX * ‖1 - z‖) := by rw [mul_one]; gcongr
        _ = lam * EX * ‖1 - z‖ := by ring
    have : mu * ‖1 - z‖ < mu * ‖1 - z‖ := by
      calc mu * ‖1 - z‖ = lam * ‖z‖ * ‖1 - C‖ := e2
        _ ≤ lam * EX * ‖1 - z‖ := this
        _ < mu * ‖1 - z‖ := mul_lt_mul_of_pos_right hst h1z
    exact lt_irrefl _ this
  -- the functional equation
  have hconv : HasSum (fun n => ((bkConv p c n : ℝ) : ℂ) * z ^ n) (P * C) := by
    have := hasSum_sum_range_mul_of_summable_norm sa sb
    refine this.congr_fun (fun n => ?_)
    unfold bkConv
    push_cast
    rw [sum_mul]
    refine sum_congr rfl (fun j hj => ?_)
    simp at hj
    rw [show z ^ n = z ^ j * z ^ (n - j) by rw [← pow_add]; congr 1; omega]
    ring
  have hPs := sa.of_norm.hasSum
  have hPsh := (hasSum_nat_add_iff' 1).mpr hPs
  simp only [range_one, sum_singleton, pow_zero, mul_one] at hPsh
  set d : ℕ → ℝ := fun n => mu * p (n + 1) - (lam + mu) * p n + lam * bkConv p c n with hd
  have hd0 : ∀ n, n ≠ 0 → d n = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := hp.2.2.1 (m + 1) (by omega)
    rw [bk_bal_sum p c hc.1] at this
    simp only [hd]
    linarith
  have hdz : d 0 = -mu * p 0 := by
    simp only [hd, bkConv, zero_add, range_one, sum_singleton, Nat.sub_self, hc.1, mul_zero]
    linarith [hp.2.2.2]
  have hS1 : HasSum (fun n => ((d n : ℝ) : ℂ) * z ^ (n + 1)) (((d 0 : ℝ) : ℂ) * z ^ (0 + 1)) :=
    hasSum_single 0 (fun n hn => by rw [hd0 n hn]; simp)
  have hS2 : HasSum (fun n => ((d n : ℝ) : ℂ) * z ^ (n + 1))
      ((mu : ℂ) * (P - (p 0 : ℂ)) - ((lam : ℂ) + mu) * z * P + (lam : ℂ) * z * (P * C)) := by
    have := ((hPsh.mul_left (mu : ℂ)).sub (hPs.mul_left (((lam : ℂ) + mu) * z))).add
      (hconv.mul_left ((lam : ℂ) * z))
    refine this.congr_fun (fun n => ?_)
    simp only [hd]
    push_cast
    ring
  have key := hS2.unique hS1
  rw [hdz] at key
  push_cast at key
  rw [eq_div_iff hden]
  linear_combination key


lemma bk_sum_range_succ_cast (k : ℕ) : ∑ m ∈ range k, ((m : ℝ) + 1) = (k : ℝ) * (k + 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

lemma bk_mean (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (c : ℕ → ℝ) (hc : IsBatchSizeDist c) (hc1 : Summable (fun n : ℕ => (n : ℝ) * c n))
    (hc2 : Summable (fun n : ℕ => (n : ℝ) ^ 2 * c n))
    (EX EX2 r ρ : ℝ) (hEX : EX = ∑' n : ℕ, (n : ℝ) * c n)
    (hEX2 : EX2 = ∑' n : ℕ, (n : ℝ) ^ 2 * c n)
    (hr : r = lam / mu) (hρ : ρ = lam * EX / mu) (hρ1 : ρ < 1)
    (p : ℕ → ℝ) (hp : IsBulkInputSteadyState lam mu c p) :
    HasSum (fun n : ℕ => (n : ℝ) * p n) (r * (EX + EX2) / (2 * (1 - ρ))) := by
  have hT := bkT_hasSum_EX c hc hc1
  rw [← hEX] at hT
  have hEX0 : 0 ≤ EX := hasSum_le (fun i => bkT_nonneg c hc i) hasSum_zero hT
  have hEX20 : 0 ≤ EX2 := by
    rw [hEX2]; exact tsum_nonneg (fun n => mul_nonneg (sq_nonneg _) (hc.2.1 n))
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hrρ : r * EX = ρ := by rw [hr, hρ]; ring
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  set U : ℕ → ℝ := fun m => ((m : ℝ) + 1) * bkT c m with hU
  have hW : HasSum (fun k => (∑ m ∈ range k, ((m : ℝ) + 1)) * c k) ((EX2 + EX) / 2) := by
    have := (hc2.hasSum.add hc1.hasSum).div_const 2
    rw [← hEX, ← hEX2] at this
    refine this.congr_fun (fun k => ?_)
    rw [bk_sum_range_succ_cast]; ring
  have hUs : HasSum U ((EX2 + EX) / 2) := by
    have := bk_tail_weighted c hc (fun m => (m : ℝ) + 1) (fun m => by positivity) hW.summable
    rw [hW.tsum_eq] at this
    exact this
  have hU0 : ∀ m, 0 ≤ U m := fun m => mul_nonneg (by positivity) (bkT_nonneg c hc m)
  have hcut := bk_cut lam mu c p hc.1 hp.2.2
  have hnn := hp.1
  have hident : ∀ n : ℕ, ((n : ℝ) + 1) * p (n + 1) = lam / mu *
      (∑ j ∈ range (n + 1), ((j : ℝ) * p j) * bkT c (n - j) +
        ∑ j ∈ range (n + 1), p j * U (n - j)) := by
    intro n
    have h1 := hcut n
    have : ((n : ℝ) + 1) * ∑ j ∈ range (n + 1), p j * bkT c (n - j) =
        ∑ j ∈ range (n + 1), ((j : ℝ) * p j) * bkT c (n - j) +
          ∑ j ∈ range (n + 1), p j * U (n - j) := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl (fun j hj => ?_)
      simp at hj
      simp only [hU]
      rw [Nat.cast_sub (by omega)]
      ring
    rw [← this]
    field_simp
    linear_combination h1
  -- partial sums bound
  have hpB : ∀ N, ∑ j ∈ range N, p j ≤ 1 :=
    fun N => sum_le_hasSum (range N) (fun i _ => hnn i) hp.2.1
  have hTB : ∀ M, ∑ m ∈ range M, bkT c m ≤ EX :=
    fun M => sum_le_hasSum (range M) (fun i _ => bkT_nonneg c hc i) hT
  have hUB : ∀ M, ∑ m ∈ range M, U m ≤ (EX2 + EX) / 2 :=
    fun M => sum_le_hasSum (range M) (fun i _ => hU0 i) hUs
  have hjp0 : ∀ j : ℕ, 0 ≤ (j : ℝ) * p j := fun j => mul_nonneg (by positivity) (hnn j)
  set K0 := r * (EX2 + EX) / 2 / (1 - ρ) with hK0
  have h1ρ : 0 < 1 - ρ := by linarith
  have hbound : ∀ N, ∑ n ∈ range N, (n : ℝ) * p n ≤ K0 := by
    intro N
    rcases N with _ | N
    · simp [hK0]; positivity
    set A := ∑ n ∈ range (N + 1), (n : ℝ) * p n with hA
    have e1 : A = ∑ n ∈ range N, ((n : ℝ) + 1) * p (n + 1) := by
      rw [hA, sum_range_succ']; push_cast; simp
    have e2 : ∑ n ∈ range N, ((n : ℝ) + 1) * p (n + 1) = lam / mu *
        (∑ n ∈ range N, ∑ j ∈ range (n + 1), ((j : ℝ) * p j) * bkT c (n - j) +
          ∑ n ∈ range N, ∑ j ∈ range (n + 1), p j * U (n - j)) := by
      rw [← sum_add_distrib, mul_sum]
      exact sum_congr rfl (fun n _ => hident n)
    have e3 := bk_conv_le (fun j => (j : ℝ) * p j) (bkT c) hjp0 EX hTB N
    have e4 := bk_conv_le p U hnn _ hUB N
    have e5 : ∑ j ∈ range N, (j : ℝ) * p j ≤ A := by
      rw [hA, sum_range_succ]; linarith [hjp0 N]
    have e6 := hpB N
    have hlm : 0 ≤ lam / mu := by positivity
    have : A ≤ ρ * A + r * (EX2 + EX) / 2 := by
      have eA := e1.trans e2
      have h7 : lam / mu * (∑ n ∈ range N, ∑ j ∈ range (n + 1), ((j : ℝ) * p j) * bkT c (n - j) +
          ∑ n ∈ range N, ∑ j ∈ range (n + 1), p j * U (n - j)) ≤
          lam / mu * ((∑ j ∈ range N, (j : ℝ) * p j) * EX + (∑ j ∈ range N, p j) * ((EX2 + EX) / 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add e3 e4) hlm
      have h8 : (∑ j ∈ range N, (j : ℝ) * p j) * EX ≤ A * EX := mul_le_mul_of_nonneg_right e5 hEX0
      have h9 : (∑ j ∈ range N, p j) * ((EX2 + EX) / 2) ≤ 1 * ((EX2 + EX) / 2) :=
        mul_le_mul_of_nonneg_right e6 (by positivity)
      have h10 : lam / mu * ((∑ j ∈ range N, (j : ℝ) * p j) * EX + (∑ j ∈ range N, p j) * ((EX2 + EX) / 2))
          ≤ lam / mu * (A * EX + 1 * ((EX2 + EX) / 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add h8 h9) hlm
      have h11 : lam / mu * (A * EX + 1 * ((EX2 + EX) / 2)) = ρ * A + r * (EX2 + EX) / 2 := by
        rw [hρ, hr]; ring
      linarith
    rw [hK0, le_div_iff₀ h1ρ]
    linarith
  have hLs : Summable (fun n : ℕ => (n : ℝ) * p n) := summable_of_sum_range_le hjp0 hbound
  set L := ∑' n : ℕ, (n : ℝ) * p n with hL
  -- exact value
  have hjn : Summable (fun n : ℕ => ‖(n : ℝ) * p n‖) := hLs.congr (fun n => (Real.norm_of_nonneg (hjp0 n)).symm)
  have hTn : Summable (fun n => ‖bkT c n‖) :=
    hT.summable.congr (fun n => (Real.norm_of_nonneg (bkT_nonneg c hc n)).symm)
  have hpn : Summable (fun n => ‖p n‖) := hp.2.1.summable.congr (fun n => (Real.norm_of_nonneg (hnn n)).symm)
  have hUn : Summable (fun n => ‖U n‖) := hUs.summable.congr (fun n => (Real.norm_of_nonneg (hU0 n)).symm)
  have c1 := hasSum_sum_range_mul_of_summable_norm hjn hTn
  have c2 := hasSum_sum_range_mul_of_summable_norm hpn hUn
  rw [hT.tsum_eq] at c1
  rw [hUs.tsum_eq, hp.2.1.tsum_eq] at c2
  have hA1 := (c1.add c2).mul_left (lam / mu)
  have hA2 : HasSum (fun n : ℕ => ((n : ℝ) + 1) * p (n + 1)) L := by
    have := (hasSum_nat_add_iff' 1).mpr hLs.hasSum
    simp only [range_one, sum_singleton, CharP.cast_eq_zero, zero_mul, sub_zero] at this
    refine this.congr_fun (fun n => ?_)
    push_cast; ring
  have hA1' : HasSum (fun n : ℕ => ((n : ℝ) + 1) * p (n + 1))
      (lam / mu * (L * EX + 1 * ((EX2 + EX) / 2))) := hA1.congr_fun (fun n => hident n)
  have hu := hA2.unique hA1'
  have hval : L = r * (EX + EX2) / (2 * (1 - ρ)) := by
    rw [eq_div_iff (by positivity)]
    have : lam / mu * (L * EX + 1 * ((EX2 + EX) / 2)) = ρ * L + r * (EX2 + EX) / 2 := by
      rw [hρ, hr]; ring
    rw [this] at hu
    linarith
  rw [← hval]
  exact hLs.hasSum


theorem bk_core (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (c : ℕ → ℝ) (hc : IsBatchSizeDist c) (hc1 : Summable (fun n : ℕ => (n : ℝ) * c n))
    (EX EX2 r ρ : ℝ) (hEX : EX = ∑' n : ℕ, (n : ℝ) * c n)
    (hEX2 : EX2 = ∑' n : ℕ, (n : ℝ) ^ 2 * c n)
    (hr : r = lam / mu) (hρ : ρ = lam * EX / mu) (hρ1 : ρ < 1) :
    (∃ p : ℕ → ℝ, IsBulkInputSteadyState lam mu c p) ∧
      ∀ p : ℕ → ℝ, IsBulkInputSteadyState lam mu c p →
        (∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 →
          cpgf p z = (mu : ℂ) * (p 0 : ℂ) * (1 - z) /
            ((mu : ℂ) * (1 - z) - (lam : ℂ) * z * (1 - cpgf c z))) ∧
        p 0 = 1 - r * EX ∧ p 0 = 1 - ρ ∧
        (Summable (fun n : ℕ => (n : ℝ) ^ 2 * c n) →
          HasSum (fun n : ℕ => (n : ℝ) * p n) (r * (EX + EX2) / (2 * (1 - ρ))) ∧
          HasSum (fun n : ℕ => (n : ℝ) * p n) ((ρ + r * EX2) / (2 * (1 - ρ)))) := by
  have hst : lam * (∑' n : ℕ, (n : ℝ) * c n) < mu := by
    rw [← hEX]
    rw [hρ, div_lt_one hmu] at hρ1
    exact hρ1
  refine ⟨bk_exists lam mu hlam hmu c hc hc1 ρ (by rw [hρ, hEX]) hρ1, fun p hp => ?_⟩
  have hp0 : p 0 = 1 - r * EX := by
    have hcut := bk_cut lam mu c p hc.1 hp.2.2
    have h1 := bk_shift_hasSum lam mu c p hc hc1 hp.1 hp.2.1.summable hcut hmu
    rw [hp.2.1.tsum_eq, ← hEX] at h1
    have h2 := (hasSum_nat_add_iff' 1).mpr hp.2.1
    simp only [range_one, sum_singleton] at h2
    have := h1.unique h2
    rw [hr]
    linarith
  have hrρ : r * EX = ρ := by rw [hr, hρ]; ring
  refine ⟨fun z hz hz1 => bk_pgf lam mu hlam hmu c hc hc1 hst p hp z hz hz1, hp0, by rw [hp0, hrρ], ?_⟩
  intro hc2
  have hm := bk_mean lam mu hlam hmu c hc hc1 hc2 EX EX2 r ρ hEX hEX2 hr hρ hρ1 p hp
  refine ⟨hm, ?_⟩
  have : (ρ + r * EX2) / (2 * (1 - ρ)) = r * (EX + EX2) / (2 * (1 - ρ)) := by
    rw [← hrρ]; ring
  rw [this]; exact hm

end QueueingFundamentals.AdvMarkov

open QueueingFundamentals.AdvMarkov


theorem solution (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (c : ℕ → ℝ) (hc : IsBatchSizeDist c) (hc1 : Summable (fun n : ℕ => (n : ℝ) * c n))
    (EX EX2 r ρ : ℝ) (hEX : EX = ∑' n : ℕ, (n : ℝ) * c n)
    (hEX2 : EX2 = ∑' n : ℕ, (n : ℝ) ^ 2 * c n)
    (hr : r = lam / mu) (hρ : ρ = lam * EX / mu) (hρ1 : ρ < 1) :
    (∃ p : ℕ → ℝ, IsBulkInputSteadyState lam mu c p) ∧
      ∀ p : ℕ → ℝ, IsBulkInputSteadyState lam mu c p →
        (∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 →
          cpgf p z = (mu : ℂ) * (p 0 : ℂ) * (1 - z) /
            ((mu : ℂ) * (1 - z) - (lam : ℂ) * z * (1 - cpgf c z))) ∧
        p 0 = 1 - r * EX ∧ p 0 = 1 - ρ ∧
        (Summable (fun n : ℕ => (n : ℝ) ^ 2 * c n) →
          HasSum (fun n : ℕ => (n : ℝ) * p n) (r * (EX + EX2) / (2 * (1 - ρ))) ∧
          HasSum (fun n : ℕ => (n : ℝ) * p n) ((ρ + r * EX2) / (2 * (1 - ρ)))) := by
  exact bk_core lam mu hlam hmu c hc hc1 EX EX2 r ρ hEX hEX2 hr hρ hρ1

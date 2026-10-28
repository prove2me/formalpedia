-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P18.logarithmic_power_threshold
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:56:43.71203+00:00
-- url     : https://prove2.me/submissions/ac0880ff-f966-402d-a332-86b0c33bdf13

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P18
noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P18

theorem S169_upper (q : ℝ) (hq : 2 < q) (lam : ℝ) (hl : 0 < lam) (n : ℕ) :
    Real.exp (-lam * logPowerLevel q n) ≤
      Real.exp (2 * (2 / lam) ^ (1 / (q - 1))) * ((n + 1 : ℝ) ^ 2)⁻¹ := by
  set X0 := (2 / lam) ^ (1 / (q - 1)) with hX0
  set L := Real.log (n + 1 : ℝ) with hL
  have hn : (1:ℝ) ≤ n + 1 := by have := n.cast_nonneg (α := ℝ); linarith
  have hL0 : 0 ≤ L := Real.log_nonneg hn
  have hX0pos : 0 ≤ X0 := Real.rpow_nonneg (by positivity) _
  have key : 2 * L - 2 * X0 ≤ lam * L ^ q := by
    rcases le_or_gt X0 L with h | h
    · have hq1 : 0 < q - 1 := by linarith
      have h1 : 2 / lam ≤ L ^ (q - 1) := by
        have : X0 ^ (q - 1) = 2 / lam := by
          rw [hX0, ← Real.rpow_mul (by positivity)]
          rw [one_div_mul_cancel hq1.ne', Real.rpow_one]
        rw [← this]
        exact Real.rpow_le_rpow hX0pos h hq1.le
      have h2 : L ^ q = L ^ (q - 1) * L := by
        rcases eq_or_lt_of_le hL0 with h0 | h0
        · rw [← h0, Real.zero_rpow (by linarith), Real.zero_rpow hq1.ne', zero_mul]
        · rw [← Real.rpow_add_one h0.ne']; ring_nf
      rw [h2]
      have : 2 ≤ lam * L ^ (q - 1) := by
        rw [div_le_iff₀ hl] at h1; linarith
      nlinarith
    · have : 0 ≤ L ^ q := Real.rpow_nonneg hL0 _
      nlinarith
  have hexpL : Real.exp (-2 * L) = ((n + 1 : ℝ) ^ 2)⁻¹ := by
    rw [show -2 * L = -(2 * L) by ring, Real.exp_neg, hL, ← Real.log_rpow (by linarith),
      Real.exp_log (by positivity)]
    norm_num
  rw [← hexpL, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [logPowerLevel]
  rw [← hL]
  linarith

theorem S169_forward (q : ℝ) (hq : 2 < q) :
    Tendsto (fun lambda : ℝ => (logPowerPartition q lambda) ^ lambda)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 : ℝ≥0∞)) := by
  set s : ℝ := ∑' n : ℕ, ((n + 1 : ℝ) ^ 2)⁻¹ with hs
  have hsum : Summable (fun n : ℕ => ((n + 1 : ℝ) ^ 2)⁻¹) := by
    have := (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
    exact_mod_cast (summable_nat_add_iff 1).mpr this
  have hspos : 0 < s := by
    have := hsum.tsum_pos (fun n => by positivity) 0 (by positivity)
    exact this
  set p : ℝ := 1 / (q - 1) with hp
  have hp0 : 0 < p := by rw [hp]; apply div_pos one_pos; linarith
  have hp1 : p < 1 := by rw [hp, div_lt_one (by linarith)]; linarith
  -- upper function
  let U : ℝ → ℝ := fun lam => Real.exp (2 * (2 ^ p * lam ^ (1 - p))) * s ^ lam
  have hU : Tendsto U (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h1 : Tendsto (fun lam : ℝ => lam ^ (1 - p)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have := (Real.continuousAt_rpow_const 0 (1 - p) (Or.inr (by linarith))).tendsto
      rw [Real.zero_rpow (by linarith)] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun lam : ℝ => s ^ lam) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have := (Real.continuousAt_const_rpow (a := s) hspos.ne').tendsto (x := 0)
      rw [Real.rpow_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h3 := ((h1.const_mul (2 ^ p)).const_mul 2).rexp.mul h2
    simpa using h3
  have hUZ : ∀ lam : ℝ, 0 < lam → (logPowerPartition q lam) ^ lam ≤ ENNReal.ofReal (U lam) := by
    intro lam hl
    have hX : (2 / lam) ^ (1 / (q - 1)) * lam = 2 ^ p * lam ^ (1 - p) := by
      rw [← hp, Real.div_rpow (by norm_num) hl.le, Real.rpow_sub hl, Real.rpow_one]
      field_simp
    have hZ : logPowerPartition q lam ≤
        ENNReal.ofReal (Real.exp (2 * (2 / lam) ^ (1 / (q - 1))) * s) := by
      unfold logPowerPartition
      rw [hs, ← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
        (hsum.mul_left _)]
      exact ENNReal.tsum_le_tsum fun n => ENNReal.ofReal_le_ofReal (S169_upper q hq lam hl n)
    calc (logPowerPartition q lam) ^ lam
        ≤ (ENNReal.ofReal (Real.exp (2 * (2 / lam) ^ (1 / (q - 1))) * s)) ^ lam :=
          ENNReal.rpow_le_rpow hZ hl.le
      _ = ENNReal.ofReal ((Real.exp (2 * (2 / lam) ^ (1 / (q - 1))) * s) ^ lam) :=
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hl.le
      _ = ENNReal.ofReal (U lam) := by
          congr 1
          simp only [U]
          rw [Real.mul_rpow (by positivity) hspos.le, ← Real.exp_mul, ← hX]
          ring_nf
  have hLZ : ∀ lam : ℝ, 0 < lam → 1 ≤ (logPowerPartition q lam) ^ lam := by
    intro lam hl
    apply ENNReal.one_le_rpow _ hl
    unfold logPowerPartition
    refine le_trans ?_ (ENNReal.le_tsum 0)
    simp [logPowerLevel, Real.zero_rpow (show q ≠ 0 by linarith)]
  have hU' : Tendsto (fun lam => ENNReal.ofReal (U lam)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using ENNReal.tendsto_ofReal hU
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with lam hl using hLZ lam hl
  · filter_upwards [self_mem_nhdsWithin] with lam hl using hUZ lam hl

theorem S169_lower (q : ℝ) (hq : q ≤ 2) (k : ℕ) (hk : 16 ≤ k) :
    ENNReal.ofReal (Real.exp (1 / 8)) ≤
      (logPowerPartition q (1 / (2 * Real.log k))) ^ (1 / (2 * Real.log k)) := by
  set X := Real.log k with hXdef
  have hk0 : (16:ℝ) ≤ k := by exact_mod_cast hk
  have hX4 : 4 * Real.log 2 ≤ X := by
    rw [hXdef, ← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by positivity) (by norm_num; linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hXpos : 0 < X := by linarith
  set lam := 1 / (2 * X) with hlam
  have hl : 0 < lam := by positivity
  -- each term with 2 ≤ n < k is ≥ exp(-X/2)
  have hterm : ∀ n ∈ Finset.Ico 2 k,
      ENNReal.ofReal (Real.exp (-X / 2)) ≤ ENNReal.ofReal (Real.exp (-lam * logPowerLevel q n)) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    set L := Real.log (n + 1 : ℝ)
    have hn2 : (3:ℝ) ≤ n + 1 := by have : (2:ℝ) ≤ n := by exact_mod_cast hn.1
                                   linarith
    have hL1 : 1 ≤ L := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have hLX : L ≤ X := Real.log_le_log (by linarith) (by
      have : (n:ℝ) + 1 ≤ k := by exact_mod_cast hn.2
      exact this)
    have h1 : L ^ q ≤ L ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 hq
    have h2 : L ^ (2:ℝ) ≤ X ^ (2:ℝ) := Real.rpow_le_rpow (by linarith) hLX (by norm_num)
    have h3 : lam * X ^ (2:ℝ) = X / 2 := by
      rw [hlam, Real.rpow_two]; field_simp
    have : lam * L ^ q ≤ X / 2 := by
      rw [← h3]; exact mul_le_mul_of_nonneg_left (h1.trans h2) hl.le
    simp only [logPowerLevel]
    linarith
  have hZ : ENNReal.ofReal (((k:ℝ) - 2) * Real.exp (-X / 2)) ≤ logPowerPartition q lam := by
    unfold logPowerPartition
    refine le_trans ?_ (ENNReal.sum_le_tsum (Finset.Ico 2 k))
    refine le_trans ?_ (Finset.sum_le_sum hterm)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, ENNReal.ofReal_mul (by linarith)]
    gcongr
    rw [show ((k:ℝ) - 2) = ((k - 2 : ℕ) : ℝ) by rw [Nat.cast_sub (by omega)]; norm_num,
      ENNReal.ofReal_natCast]
  have hk2 : (k:ℝ) = Real.exp X := by rw [hXdef, Real.exp_log (by linarith)]
  have hreal : Real.exp (1 / 8) ≤ (((k:ℝ) - 2) * Real.exp (-X / 2)) ^ lam := by
    have hA : Real.exp (X / 2 - Real.log 2) ≤ ((k:ℝ) - 2) * Real.exp (-X / 2) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num)]
      have e1 : Real.exp (X / 2) = Real.exp X * Real.exp (-X / 2) := by
        rw [← Real.exp_add]; ring_nf
      rw [e1, ← hk2]
      have : 0 < Real.exp (-X / 2) := Real.exp_pos _
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    calc Real.exp (1 / 8) ≤ Real.exp (X / 2 - Real.log 2) ^ lam := by
          rw [← Real.exp_mul]
          apply Real.exp_le_exp.mpr
          rw [hlam]
          rw [show (X / 2 - Real.log 2) * (1 / (2 * X)) = 1 / 4 - Real.log 2 / (2 * X) by
            field_simp; ring]
          have : Real.log 2 / (2 * X) ≤ 1 / 8 := by
            rw [div_le_iff₀ (by positivity)]; linarith
          linarith
      _ ≤ (((k:ℝ) - 2) * Real.exp (-X / 2)) ^ lam :=
          Real.rpow_le_rpow (Real.exp_pos _).le hA hl.le
  calc ENNReal.ofReal (Real.exp (1 / 8))
      ≤ ENNReal.ofReal ((((k:ℝ) - 2) * Real.exp (-X / 2)) ^ lam) := ENNReal.ofReal_le_ofReal hreal
    _ = (ENNReal.ofReal (((k:ℝ) - 2) * Real.exp (-X / 2))) ^ lam :=
        (ENNReal.ofReal_rpow_of_nonneg (by nlinarith [Real.exp_pos (-X/2)]) hl.le).symm
    _ ≤ (logPowerPartition q lam) ^ lam := ENNReal.rpow_le_rpow hZ hl.le

theorem S169_main (q : ℝ) :
    Tendsto (fun lambda : ℝ => (logPowerPartition q lambda) ^ lambda)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 : ℝ≥0∞)) ↔ 2 < q := by
  constructor
  · intro h
    by_contra hq
    push Not at hq
    have hseq : Tendsto (fun k : ℕ => 1 / (2 * Real.log k)) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have : Tendsto (fun k : ℕ => 2 * Real.log k) atTop atTop :=
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
        have e : (fun k : ℕ => 1 / (2 * Real.log k)) = (fun k : ℕ => 2 * Real.log k)⁻¹ := by
          funext k; simp
        rw [e]; exact this.inv_tendsto_atTop
      · filter_upwards [eventually_ge_atTop 2] with k hk
        have : (1:ℝ) < k := by exact_mod_cast hk
        have := Real.log_pos this
        simp only [Set.mem_Ioi]; positivity
    have hc := h.comp hseq
    have hge : ENNReal.ofReal (Real.exp (1 / 8)) ≤ 1 :=
      ge_of_tendsto hc (by
        filter_upwards [eventually_ge_atTop 16] with k hk using S169_lower q hq k hk)
    rw [ENNReal.ofReal_le_one] at hge
    have := Real.add_one_le_exp (1 / 8 : ℝ)
    linarith
  · exact S169_forward q

end QAlgorithms.Papers.Independent.Support50.P18

open QAlgorithms.Papers.Independent.Support50.P18 in
theorem solution (q : ℝ) :
    Tendsto (fun lambda : ℝ => (logPowerPartition q lambda) ^ lambda)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 : ℝ≥0∞)) ↔ 2 < q :=
  S169_main q

end

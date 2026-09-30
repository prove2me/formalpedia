-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_auxiliary_period_jet_systems
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T15:57:12.261704+00:00
-- url     : https://prove2.me/submissions/b92c6d86-9c5b-45e7-a326-123f2328b794

import Definitions.Def_WeierstrassEllipticZeta_PeriodJetBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter
open scoped Polynomial

open WeierstrassEllipticZeta

private lemma period_index_bound (N : ℕ) (hN : (2 : ℝ) ≤ N) :
    (1 + 3 * auxiliaryS3 N : ℝ) ≤ (N : ℝ) ^ 4 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlog : Real.log N ≤ N := (Real.log_le_sub_one_of_pos hN0).trans (by linarith)
  have hp : (N : ℝ) ^ (5 / 8 : ℝ) ≤ N := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (5 / 8 : ℝ) ≤ 1)
  have hq := Nat.floor_le (by positivity :
    0 ≤ (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N / 64)
  have hprod := mul_le_mul hp hlog hlog0 (by positivity : (0 : ℝ) ≤ N)
  change (auxiliaryS3 N : ℝ) ≤ _ at hq
  have hq2 : (auxiliaryS3 N : ℝ) ≤ (N : ℝ) ^ 2 := by
    nlinarith only [hq, hprod, sq_nonneg (N : ℝ)]
  have hsq : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hN]
  nlinarith only [hq2, hsq, sq_nonneg ((N : ℝ) ^ 2 - 4)]

private lemma period_jet_numerical_bounds (B H K E : ℕ) (hH : 0 < H) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
      ∀ m l n : ℕ, ∀ a : ℤ,
        (m : ℝ) * Real.log N ≤ N → l ≤ m → n ≤ K * m →
        a.natAbs ≤ 3 * auxiliaryS3 N →
        let D := B * ((K + 3) * m)
        (D : ℝ) ≤ A * m ∧
        (m + 1 : ℝ) * (l + 1 : ℝ) ^ 2 * (E + 1) * (D + 1) ≤
          Real.exp (A * N) ∧
        ((n.factorial * 24 ^ (m + 2 * l + n) * (1 + a.natAbs) ^ (m + l) *
          H ^ (m + 2 * l + n + 1) : ℕ) : ℝ) ≤ Real.exp (A * N) := by
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH1
  have hlog24 : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
  let A : ℝ := B * (K + 3) + E + 12 + K +
    Real.log 24 * (K + 3) + Real.log H * (K + 4)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog := Real.tendsto_log_atTop.comp hcast
  filter_upwards [hcast.eventually_ge_atTop 2,
    hlog.eventually_ge_atTop (max 1 (K : ℝ))] with N hN hlogN m l n a hm hl hn ha
  dsimp only [Function.comp_def] at hlogN
  have hlog1 : 1 ≤ Real.log N := (le_max_left _ _).trans hlogN
  have hlogK : (K : ℝ) ≤ Real.log N := (le_max_right _ _).trans hlogN
  have hN0 : (0 : ℝ) < N := by linarith only [hN]
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hmN : (m : ℝ) ≤ N := by
    nlinarith only [hm, mul_le_mul_of_nonneg_left hlog1 hm0]
  have hlm : (l : ℝ) ≤ m := by exact_mod_cast hl
  have hnKm : (n : ℝ) ≤ K * m := by exact_mod_cast hn
  have hnlog : (n : ℝ) * Real.log N ≤ K * N := by
    have h1 := mul_le_mul_of_nonneg_right hnKm (by linarith : 0 ≤ Real.log N)
    have h2 := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ K)
    nlinarith only [h1, h2]
  have hnN : (n : ℝ) ≤ N := by
    have h := mul_le_mul_of_nonneg_right hlogK (le_of_lt hN0)
    nlinarith only [hnlog, h, hlog1]
  have hJ : (m + 2 * l + n : ℕ) ≤ (K + 3) * m := by nlinarith only [hl, hn]
  have hJR : (m + 2 * l + n : ℝ) ≤ (K + 3) * m := by exact_mod_cast hJ
  have hJN : (m + 2 * l + n : ℝ) ≤ (K + 3) * N :=
    hJR.trans (mul_le_mul_of_nonneg_left hmN (by positivity))
  have hJ1 : (m + 2 * l + n + 1 : ℝ) ≤ (K + 4) * N := by
    nlinarith only [hJN, hN]
  have hfact : (n.factorial : ℝ) ≤ Real.exp (K * N) := by
    calc
      _ ≤ (n : ℝ) ^ n := by exact_mod_cast n.factorial_le_pow
      _ ≤ (N : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hnN n
      _ = Real.exp ((n : ℝ) * Real.log N) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hN0, mul_comm]
      _ ≤ _ := Real.exp_le_exp.mpr hnlog
  have hbase : (1 + a.natAbs : ℝ) ≤ (N : ℝ) ^ 4 := by
    have haR : (a.natAbs : ℝ) ≤ 3 * auxiliaryS3 N := by exact_mod_cast ha
    exact (by linarith : (1 + a.natAbs : ℝ) ≤ 1 + 3 * auxiliaryS3 N).trans
      (period_index_bound N hN)
  have haper : (1 + a.natAbs : ℝ) ^ (m + l) ≤ Real.exp (8 * N) := by
    calc
      _ ≤ ((N : ℝ) ^ 4) ^ (m + l) := pow_le_pow_left₀ (by positivity) hbase _
      _ = Real.exp (4 * (m + l) * Real.log N) := by
        rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos hN0]
        push_cast
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_right hlm (by linarith : 0 ≤ Real.log N)
        nlinarith only [h, hm]
  have h24 : (24 : ℝ) ^ (m + 2 * l + n) ≤
      Real.exp (Real.log 24 * (K + 3) * N) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 24)]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hJN hlog24]
  have hHp : (H : ℝ) ^ (m + 2 * l + n + 1) ≤
      Real.exp (Real.log H * (K + 4) * N) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hH0]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hJ1 hlogH]
  let D := B * ((K + 3) * m)
  have hD : (D : ℝ) = B * (K + 3) * m := by dsimp [D]; push_cast; ring
  have hDN : (D : ℝ) ≤ B * (K + 3) * N := by
    rw [hD]
    exact mul_le_mul_of_nonneg_left hmN (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · change (D : ℝ) ≤ A * m
    rw [hD]
    apply mul_le_mul_of_nonneg_right _ hm0
    dsimp [A]
    nlinarith only [Nat.cast_nonneg (α := ℝ) E, Nat.cast_nonneg (α := ℝ) K,
      mul_nonneg hlogH (show (0 : ℝ) ≤ K + 4 by positivity),
      mul_nonneg hlog24 (show (0 : ℝ) ≤ K + 3 by positivity)]
  · change (m + 1 : ℝ) * (l + 1 : ℝ) ^ 2 * (E + 1) * (D + 1) ≤ _
    have hmexp : (m + 1 : ℝ) ≤ Real.exp N :=
      (by linarith : (m + 1 : ℝ) ≤ N + 1).trans (Real.add_one_le_exp _)
    have hlexp : (l + 1 : ℝ) ≤ Real.exp N :=
      (by linarith : (l + 1 : ℝ) ≤ N + 1).trans (Real.add_one_le_exp _)
    have hEexp : (E + 1 : ℝ) ≤ Real.exp ((E : ℝ) * N) :=
      (Real.add_one_le_exp _).trans (Real.exp_le_exp.mpr (by nlinarith only [hN, Nat.cast_nonneg (α := ℝ) E]))
    have hDexp : (D + 1 : ℝ) ≤ Real.exp (B * (K + 3) * N) :=
      (Real.add_one_le_exp _).trans (Real.exp_le_exp.mpr hDN)
    calc
      _ ≤ Real.exp N * (Real.exp N) ^ 2 * Real.exp ((E : ℝ) * N) *
          Real.exp (B * (K + 3) * N) := by
        apply mul_le_mul _ hDexp (by positivity) (by positivity)
        apply mul_le_mul _ hEexp (by positivity) (by positivity)
        exact mul_le_mul hmexp (pow_le_pow_left₀ (by positivity) hlexp 2)
          (by positivity) (by positivity)
      _ = Real.exp ((3 + E + B * (K + 3)) * N) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hN0)
        dsimp [A]
        nlinarith only [hlogH, hlog24, Nat.cast_nonneg (α := ℝ) K,
          mul_nonneg hlogH (show (0 : ℝ) ≤ K + 4 by positivity),
          mul_nonneg hlog24 (show (0 : ℝ) ≤ K + 3 by positivity)]
  · push_cast
    calc
      _ ≤ Real.exp (K * N) * Real.exp (Real.log 24 * (K + 3) * N) *
          Real.exp (8 * N) * Real.exp (Real.log H * (K + 4) * N) := by
        apply mul_le_mul _ hHp (by positivity) (by positivity)
        apply mul_le_mul _ haper (by positivity) (by positivity)
        exact mul_le_mul hfact h24 (by positivity) (by positivity)
      _ = Real.exp ((K + 8 + Real.log 24 * (K + 3) + Real.log H * (K + 4)) * N) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hN0)
        dsimp [A]
        nlinarith only [Nat.cast_nonneg (α := ℝ) E,
          mul_nonneg (Nat.cast_nonneg (α := ℝ) B) (show (0 : ℝ) ≤ K + 3 by positivity)]

theorem solution
    (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ) (g : ℤ[X][X]) (d : ℤ[X])
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (h_period_jets : PeriodArithmeticJetSystemData L ω (u₁ / 2) θ ν g d) :
    BoundedAuxiliaryPeriodJetData L ω (u₁ / 2) θ ν g d := by
  obtain ⟨B, H, hB, hH, hjets⟩ := h_period_jets
  intro K
  obtain ⟨A, hA, hnum⟩ := period_jet_numerical_bounds B H K g.natDegree hH
  refine ⟨A, hA, ?_⟩
  filter_upwards [h_parameters 1 (by norm_num), hnum] with N hp hnum
  dsimp only at hp ⊢
  obtain ⟨hm, hl, hs, hq, hsq, hdim, hcount, hcount', hmlog, hls, hrest⟩ := hp
  have hlm : auxiliaryL N ≤ auxiliaryL0 N := by
    have : 1 ≤ auxiliaryS N ^ 2 := one_le_pow₀ (by omega : 1 ≤ auxiliaryS N)
    nlinarith only [hls, this]
  let D := B * ((K + 3) * auxiliaryL0 N)
  have hzero := hnum (auxiliaryL0 N) (auxiliaryL N) 0 0 hmlog hlm (by omega) (by simp)
  refine ⟨D, hzero.1, hzero.2.1, ?_⟩
  intro a ha
  obtain ⟨R, hR, heval, hkernel⟩ := hjets a (auxiliaryL N) (auxiliaryL0 N)
    (K * auxiliaryL0 N + 1)
  refine ⟨R, ?_, heval, ?_⟩
  · intro n i
    have hn : n.val ≤ K * auxiliaryL0 N := Nat.le_of_lt_succ n.isLt
    have hJ : auxiliaryL0 N + 2 * auxiliaryL N + n.val ≤ (K + 3) * auxiliaryL0 N := by
      nlinarith only [hlm, hn]
    obtain ⟨hy, hx, hlen⟩ := hR n i
    refine ⟨hy, fun j => (hx j).trans (Nat.mul_le_mul_left B hJ), ?_⟩
    exact (show ((∑ j ∈ (R n i).support, ∑ k ∈ ((R n i).coeff j).support,
      (((R n i).coeff j).coeff k).natAbs) : ℝ) ≤ _ by exact_mod_cast hlen).trans
      (hnum (auxiliaryL0 N) (auxiliaryL N) n a hmlog hlm hn ha).2.2
  · intro c
    simpa only [Nat.lt_succ_iff] using hkernel c


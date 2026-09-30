-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_auxiliary_nonlattice_jet_systems
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T16:19:55.196713+00:00
-- url     : https://prove2.me/submissions/b2bac0fb-a3ef-455f-bf47-d4b04f7bb773

import Definitions.Def_WeierstrassEllipticZeta_NonlatticeJetBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter
open scoped Polynomial

open WeierstrassEllipticZeta

private lemma nonlattice_weighted_degree (C K m l s n : ℕ)
    (hl : l ≤ m) (hls : l * s ^ 2 ≤ m) (hn : n ≤ K * m) :
    (∑ a, nonlatticeJetWeight m l n a * nonlatticeCoordinateDegree C s a) ≤
      C * (40 + 4 * K) * m := by
  calc
    _ = C * (5 * m + 15 * l * s ^ 2 + 20 * l + 4 * n) := by
      simp [nonlatticeJetWeight, nonlatticeCoordinateDegree, Fin.sum_univ_succ]
      ring
    _ ≤ C * ((40 + 4 * K) * m) :=
      Nat.mul_le_mul_left C (by nlinarith only [hl, hls, hn])
    _ = _ := by ring

private lemma nonlattice_jet_numerical_bounds (B H K C E : ℕ) (hH : 0 < H) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
      ∀ m l s n : ℕ, ∀ h : Fin 8 → ℕ,
        (m : ℝ) * Real.log N ≤ N → l ≤ m → l * s ^ 2 ≤ m → n ≤ K * m →
        (∀ a, (h a : ℝ) ≤ Real.exp (nonlatticeCoordinateLogBound C N s a)) →
        let D := B * (C * (40 + 4 * K) * m)
        (D : ℝ) ≤ A * m ∧
        (m + 1 : ℝ) * (l + 1 : ℝ) ^ 2 * (E + 1) * (D + 1) ≤ Real.exp (A * N) ∧
        (((n.factorial * 2 ^ (41 * (m + l + n)) *
          ∏ a, h a ^ nonlatticeJetWeight m l n a) *
          H ^ ((∑ a, nonlatticeJetWeight m l n a * nonlatticeCoordinateDegree C s a) + 1)
            : ℕ) : ℝ) ≤ Real.exp (A * N) := by
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  let F : ℝ := C * (40 + 4 * K)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let A : ℝ := B * F + E + 4 + K + Real.log 2 * 41 * (K + 2) +
    C * (55 + 4 * K) + Real.log H * (F + 1)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog := Real.tendsto_log_atTop.comp hcast
  filter_upwards [hcast.eventually_ge_atTop 2,
    hlog.eventually_ge_atTop (max 1 (K : ℝ))] with N hN hlogN m l s n h hm hl hls hn hh
  dsimp only [Function.comp_def] at hlogN
  have hlog1 : 1 ≤ Real.log N := (le_max_left _ _).trans hlogN
  have hlogK : (K : ℝ) ≤ Real.log N := (le_max_right _ _).trans hlogN
  have hlog0 : 0 ≤ Real.log N := by linarith only [hlog1]
  have hN0 : (0 : ℝ) < N := by linarith only [hN]
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hmN : (m : ℝ) ≤ N := by
    nlinarith only [hm, mul_le_mul_of_nonneg_left hlog1 hm0]
  have hlm : (l : ℝ) ≤ m := by exact_mod_cast hl
  have hlN : (l : ℝ) ≤ N := hlm.trans hmN
  have hlsR : (l : ℝ) * (s : ℝ) ^ 2 ≤ m := by exact_mod_cast hls
  have hnKm : (n : ℝ) ≤ K * m := by exact_mod_cast hn
  have hnKN : (n : ℝ) ≤ K * N :=
    hnKm.trans (mul_le_mul_of_nonneg_left hmN (by positivity))
  have hnlog : (n : ℝ) * Real.log N ≤ K * N := by
    have h1 := mul_le_mul_of_nonneg_right hnKm hlog0
    have h2 := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ K)
    nlinarith only [h1, h2]
  have hnN : (n : ℝ) ≤ N := by
    have h1 := mul_le_mul_of_nonneg_right hlogK (le_of_lt hN0)
    nlinarith only [hnlog, h1, hlog1]
  have hfact : (n.factorial : ℝ) ≤ Real.exp (K * N) := by
    calc
      _ ≤ (n : ℝ) ^ n := by exact_mod_cast n.factorial_le_pow
      _ ≤ (N : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hnN n
      _ = Real.exp ((n : ℝ) * Real.log N) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hN0, mul_comm]
      _ ≤ _ := Real.exp_le_exp.mpr hnlog
  have hweightedlog :
      (∑ a, (nonlatticeJetWeight m l n a : ℝ) * nonlatticeCoordinateLogBound C N s a) ≤
        C * (55 + 4 * K) * N := by
    calc
      _ = C * (m * Real.log N + 15 * l * (s : ℝ) ^ 2 + 15 * l * Real.log N +
          4 * m + 20 * l + 4 * n) := by
        simp [nonlatticeJetWeight, nonlatticeCoordinateLogBound, Fin.sum_univ_succ]
        ring
      _ ≤ C * ((55 + 4 * K) * N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ C)
        have hllog := (mul_le_mul_of_nonneg_right hlm hlog0).trans hm
        nlinarith only [hm, hlsR.trans hmN, hllog, hmN, hlN, hnKN]
      _ = _ := by ring
  have hprod : ((∏ a, h a ^ nonlatticeJetWeight m l n a : ℕ) : ℝ) ≤
      Real.exp (C * (55 + 4 * K) * N) := by
    push_cast
    calc
      _ ≤ ∏ a, Real.exp (nonlatticeCoordinateLogBound C N s a) ^
          nonlatticeJetWeight m l n a := by
        exact Finset.prod_le_prod (fun a _ => by positivity)
          (fun a _ => pow_le_pow_left₀ (by positivity) (hh a) _)
      _ = Real.exp (∑ a, (nonlatticeJetWeight m l n a : ℝ) *
          nonlatticeCoordinateLogBound C N s a) := by
        simp only [← Real.exp_nat_mul, Real.exp_sum]
      _ ≤ _ := Real.exp_le_exp.mpr hweightedlog
  have hpow2 : (2 : ℝ) ^ (41 * (m + l + n)) ≤
      Real.exp (Real.log 2 * 41 * (K + 2) * N) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    push_cast
    have hsum : (m + l + n : ℝ) ≤ (K + 2) * N := by
      nlinarith only [hmN, hlN, hnKN]
    nlinarith only [mul_le_mul_of_nonneg_left hsum hlog2]
  have hdeg := nonlattice_weighted_degree C K m l s n hl hls hn
  have hdegR : ((∑ a, nonlatticeJetWeight m l n a * nonlatticeCoordinateDegree C s a) : ℝ)
      ≤ F * m := by dsimp [F]; exact_mod_cast hdeg
  have hdegN : ((∑ a, nonlatticeJetWeight m l n a * nonlatticeCoordinateDegree C s a) : ℝ)
      ≤ F * N := hdegR.trans (mul_le_mul_of_nonneg_left hmN hF)
  have hHp : (H : ℝ) ^ ((∑ a, nonlatticeJetWeight m l n a *
      nonlatticeCoordinateDegree C s a) + 1) ≤ Real.exp (Real.log H * (F + 1) * N) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hH0]
    apply Real.exp_le_exp.mpr
    push_cast
    have h1 : ((∑ a, nonlatticeJetWeight m l n a * nonlatticeCoordinateDegree C s a) : ℝ)
        + 1 ≤ (F + 1) * N := by nlinarith only [hdegN, hN]
    nlinarith only [mul_le_mul_of_nonneg_left h1 hlogH]
  let D := B * (C * (40 + 4 * K) * m)
  have hD : (D : ℝ) = B * F * m := by dsimp [D, F]; push_cast; ring
  have hDN : (D : ℝ) ≤ B * F * N := by
    rw [hD]
    exact mul_le_mul_of_nonneg_left hmN (by positivity)
  have hBF : B * F + E + 3 ≤ A := by
    dsimp [A]
    nlinarith only [Nat.cast_nonneg (α := ℝ) K,
      mul_nonneg hlog2 (show (0 : ℝ) ≤ 41 * (K + 2) by positivity),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) C) (show (0 : ℝ) ≤ 55 + 4 * K by positivity),
      mul_nonneg hlogH (show 0 ≤ F + 1 by positivity)]
  refine ⟨?_, ?_, ?_⟩
  · change (D : ℝ) ≤ A * m
    rw [hD]
    apply mul_le_mul_of_nonneg_right _ hm0
    nlinarith only [hBF, Nat.cast_nonneg (α := ℝ) E]
  · change (m + 1 : ℝ) * (l + 1 : ℝ) ^ 2 * (E + 1) * (D + 1) ≤ _
    have hmexp : (m + 1 : ℝ) ≤ Real.exp N :=
      (by linarith : (m + 1 : ℝ) ≤ N + 1).trans (Real.add_one_le_exp _)
    have hlexp : (l + 1 : ℝ) ≤ Real.exp N :=
      (by linarith : (l + 1 : ℝ) ≤ N + 1).trans (Real.add_one_le_exp _)
    have hEexp : (E + 1 : ℝ) ≤ Real.exp ((E : ℝ) * N) :=
      (Real.add_one_le_exp _).trans (Real.exp_le_exp.mpr
        (by nlinarith only [hN, Nat.cast_nonneg (α := ℝ) E]))
    have hDexp : (D + 1 : ℝ) ≤ Real.exp (B * F * N) :=
      (Real.add_one_le_exp _).trans (Real.exp_le_exp.mpr hDN)
    calc
      _ ≤ Real.exp N * (Real.exp N) ^ 2 * Real.exp ((E : ℝ) * N) * Real.exp (B * F * N) := by
        apply mul_le_mul _ hDexp (by positivity) (by positivity)
        apply mul_le_mul _ hEexp (by positivity) (by positivity)
        exact mul_le_mul hmexp (pow_le_pow_left₀ (by positivity) hlexp 2)
          (by positivity) (by positivity)
      _ = Real.exp ((B * F + E + 3) * N) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hBF (le_of_lt hN0))
  · push_cast at hprod ⊢
    calc
      _ ≤ Real.exp (K * N) * Real.exp (Real.log 2 * 41 * (K + 2) * N) *
          Real.exp (C * (55 + 4 * K) * N) * Real.exp (Real.log H * (F + 1) * N) := by
        apply mul_le_mul _ hHp (by positivity) (by positivity)
        apply mul_le_mul _ hprod (by positivity) (by positivity)
        exact mul_le_mul hfact hpow2 (by positivity) (by positivity)
      _ = Real.exp ((K + Real.log 2 * 41 * (K + 2) + C * (55 + 4 * K) +
          Real.log H * (F + 1)) * N) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hN0)
        dsimp [A]
        nlinarith only [Nat.cast_nonneg (α := ℝ) E,
          mul_nonneg (Nat.cast_nonneg (α := ℝ) B) hF]

theorem solution
    (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ) (g : ℤ[X][X])
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (h_jet_systems : ReducedArithmeticJetSystemData L θ ν g) :
    BoundedAuxiliaryNonlatticeJetData L θ ν g := by
  obtain ⟨B, H, hB, hH, hjets⟩ := h_jet_systems
  intro K C
  obtain ⟨A, hA, hnum⟩ := nonlattice_jet_numerical_bounds B H K C g.natDegree hH
  refine ⟨A, hA, ?_⟩
  filter_upwards [h_parameters 1 (by norm_num), hnum] with N hp hnum
  dsimp only at hp ⊢
  obtain ⟨hm, hl, hs, hq, hsq, hdim, hcount, hcount', hmlog, hls, hrest⟩ := hp
  have hlm : auxiliaryL N ≤ auxiliaryL0 N := by
    have : 1 ≤ auxiliaryS N ^ 2 := one_le_pow₀ (by omega : 1 ≤ auxiliaryS N)
    nlinarith only [hls, this]
  let D := B * (C * (40 + 4 * K) * auxiliaryL0 N)
  have hzero := hnum (auxiliaryL0 N) (auxiliaryL N) (auxiliaryS N) 0 (fun _ => 0)
    hmlog hlm hls (by omega) (fun _ => by simpa using (Real.exp_pos _).le)
  refine ⟨D, hzero.1, hzero.2.1, ?_⟩
  intro p q h hpdeg hqdeg hplen hqlen hh
  obtain ⟨R, hR, heval⟩ := hjets (auxiliaryL N) (auxiliaryL0 N)
    (K * auxiliaryL0 N + 1) p q (nonlatticeCoordinateDegree C (auxiliaryS N)) h
    hpdeg hqdeg hplen hqlen
  refine ⟨R, ?_, ?_⟩
  · intro n i
    have hn : n.val ≤ K * auxiliaryL0 N := Nat.le_of_lt_succ n.isLt
    have hdeg := nonlattice_weighted_degree C K (auxiliaryL0 N) (auxiliaryL N)
      (auxiliaryS N) n hlm hls hn
    obtain ⟨hy, hx, hlen⟩ := hR n i
    refine ⟨hy, fun j => (hx j).trans (Nat.mul_le_mul_left B hdeg), ?_⟩
    exact (show ((∑ j ∈ (R n i).support, ∑ a ∈ ((R n i).coeff j).support,
      (((R n i).coeff j).coeff a).natAbs) : ℝ) ≤ _ by exact_mod_cast hlen).trans
      (hnum (auxiliaryL0 N) (auxiliaryL N) (auxiliaryS N) n h hmlog hlm hls hn hh).2.2
  · intro v z hv hz hzv hcoords
    obtain ⟨hvalue, hkernel⟩ := heval v z hv hz hzv hcoords
    refine ⟨hvalue, ?_⟩
    intro hzv' hq c
    simpa only [Nat.lt_succ_iff] using hkernel hzv' hq c


-- Prove2me | solution 1 for OutlierAssort.ActiveElim.regret_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T17:21:41.75132+00:00
-- url     : https://prove2.me/submissions/0332d32b-18a1-4f84-96aa-53c49f90c7b7

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_OutlierAssort_ActiveElim_Model
import Definitions.Def_OutlierAssort_ActiveElim_Algorithm

open OutlierAssort.ActiveElim

namespace OARsb

theorem epochStart_succ (N K T τ : ℕ) :
    epochStart N K T (τ + 1) = epochStart N K T τ + epochLen N K T τ := by
  simp [epochStart, Finset.sum_range_succ]

theorem epochStart_mono (N K T : ℕ) {τ τ' : ℕ} (h : τ ≤ τ') :
    epochStart N K T τ ≤ epochStart N K T τ' := by
  unfold epochStart
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem epochLen_pos {N K T : ℕ} (h0 : 1 ≤ T0 N K T) (τ : ℕ) : 1 ≤ epochLen N K T τ := by
  unfold epochLen
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by omega))

theorem epochOf_spec {N K T : ℕ} (t : ℕ) :
    epochStart N K T (epochOf N K T t) ≤ t ∧ epochOf N K T t ≤ t := by
  classical
  unfold epochOf
  have hne : ((Finset.range (t + 1)).filter (fun τ => epochStart N K T τ ≤ t)).Nonempty :=
    ⟨0, Finset.mem_filter.2 ⟨by simp, by simp [epochStart]⟩⟩
  obtain ⟨τ, hτ, heq⟩ := Finset.exists_mem_eq_sup _ hne id
  convert (show epochStart N K T τ ≤ t ∧ τ ≤ t from ?_) using 2 <;> try simp only [heq, id]
  simp only [Finset.mem_filter, Finset.mem_range] at hτ
  exact ⟨hτ.2, by omega⟩


theorem epochStart_add_T0 (N K T : ℕ) (τ : ℕ) :
    epochStart N K T τ + T0 N K T = 2 ^ τ * T0 N K T := by
  induction τ with
  | zero => simp [epochStart]
  | succ τ ih => rw [epochStart_succ, epochLen, pow_succ]; linarith

theorem t_mul_sqrt (t x : ℝ) (ht : 0 < t) (hx : 0 ≤ x) : t * Real.sqrt (x / t) = Real.sqrt (x * t) := by
  calc t * Real.sqrt (x / t) = Real.sqrt (t ^ 2) * Real.sqrt (x / t) := by rw [Real.sqrt_sq ht.le]
    _ = Real.sqrt (t ^ 2 * (x / t)) := (Real.sqrt_mul (sq_nonneg t) _).symm
    _ = Real.sqrt (x * t) := by congr 1; field_simp

/-- The per-epoch bound. -/
theorem term_bound (epsBar : ℝ) (he : 0 ≤ epsBar) (T N K t n : ℕ) (hK : 1 ≤ K) (ht : 1 ≤ t)
    (htT : t ≤ T) (hn : n ≤ N) (hL : 0 ≤ Real.log (T : ℝ)) :
    8 * (t : ℝ) * deltaHat epsBar T K t n ≤
      130 * K ^ 2 * epsBar * T + 256 * K ^ 2 * Real.sqrt epsBar * Real.sqrt (N * T * Real.log T) +
        171 * K ^ 2 * N * Real.log T + 128 * Real.sqrt K * Real.sqrt (N * T * Real.log T) := by
  set L := Real.log (T : ℝ) with hLdef
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have htTr : (t : ℝ) ≤ T := by exact_mod_cast htT
  have hnr : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hT0 : (0 : ℝ) < T := by linarith
  have hK1 : (K : ℝ) + 1 ≤ 2 * K := by linarith
  have hKK : (K : ℝ) * (K + 1) ≤ 2 * K ^ 2 := by nlinarith
  have hS1 : 0 ≤ Real.sqrt epsBar * Real.sqrt (N * T * L) := by positivity
  have hS2 : 0 ≤ Real.sqrt K * Real.sqrt (N * T * L) := by positivity
  have hP3 : 0 ≤ 171 * (K : ℝ) ^ 2 * N * L := by positivity
  have hP1 : 0 ≤ 130 * (K : ℝ) ^ 2 * epsBar * T := by positivity
  unfold deltaHat
  split_ifs with hc
  · -- short epoch
    have h1 : 8 * (t : ℝ) ≤ 2 * epsBar * T := by
      have : (t : ℝ) * (4 * ((K : ℝ) + 1)) < epsBar * T := (lt_div_iff₀ (by positivity)).1 hc
      nlinarith
    have h2 : 2 * epsBar * T ≤ 130 * (K : ℝ) ^ 2 * epsBar * T := by
      have : (1 : ℝ) ≤ K ^ 2 := one_le_pow₀ hKr
      have : 0 ≤ epsBar * T := by positivity
      nlinarith
    nlinarith
  · set m := min 1 (epsBar * T / t) with hm
    have hm0 : 0 ≤ m := le_min zero_le_one (by positivity)
    have hmt : m * t ≤ epsBar * T := by
      have : m ≤ epsBar * T / t := min_le_right _ _
      calc m * t ≤ (epsBar * T / t) * t := mul_le_mul_of_nonneg_right this ht0.le
        _ = epsBar * T := by field_simp
    -- piece a
    have ha : 64 * (K * ((K : ℝ) + 1)) * (m * t) ≤ 128 * K ^ 2 * (epsBar * T) := by
      have := mul_le_mul hKK hmt (by positivity) (by positivity)
      nlinarith
    -- piece b
    have hb0 : (t : ℝ) * Real.sqrt (m * n * L / t) = Real.sqrt (m * n * L * t) :=
      t_mul_sqrt _ _ ht0 (by positivity)
    have hb1 : Real.sqrt (m * n * L * t) ≤ Real.sqrt epsBar * Real.sqrt (N * T * L) := by
      rw [← Real.sqrt_mul he]
      apply Real.sqrt_le_sqrt
      have : m * n * L * t = (m * t) * (n * L) := by ring
      rw [this]
      have e2 : epsBar * (N * T * L) = (epsBar * T) * (N * L) := by ring
      rw [e2]
      exact mul_le_mul hmt (mul_le_mul_of_nonneg_right hnr hL) (by positivity) (by positivity)
    have hb : 128 * (K * ((K : ℝ) + 1)) * ((t : ℝ) * Real.sqrt (m * n * L / t)) ≤
        256 * K ^ 2 * (Real.sqrt epsBar * Real.sqrt (N * T * L)) := by
      rw [hb0]
      have := mul_le_mul hKK hb1 (Real.sqrt_nonneg _) (by positivity)
      nlinarith
    -- piece c
    have hc0 : (t : ℝ) * (2 * n * L / (3 * t)) = 2 * n * L / 3 := by field_simp
    have hcc : 128 * (K * ((K : ℝ) + 1)) * ((t : ℝ) * (2 * n * L / (3 * t))) ≤
        171 * K ^ 2 * N * L := by
      rw [hc0]
      have h1 : (n : ℝ) * L ≤ N * L := mul_le_mul_of_nonneg_right hnr hL
      have h2 : 0 ≤ (n : ℝ) * L := by positivity
      have := mul_le_mul hKK h1 h2 (by positivity)
      nlinarith
    -- piece d
    have hd0 : (t : ℝ) * Real.sqrt (K * n * L / t) = Real.sqrt (K * n * L * t) :=
      t_mul_sqrt _ _ ht0 (by positivity)
    have hd1 : Real.sqrt (K * n * L * t) ≤ Real.sqrt K * Real.sqrt (N * T * L) := by
      rw [← Real.sqrt_mul (by positivity)]
      apply Real.sqrt_le_sqrt
      have : (K : ℝ) * n * L * t = K * ((n * L) * t) := by ring
      rw [this]
      have e2 : (K : ℝ) * (N * T * L) = K * ((N * L) * T) := by ring
      rw [e2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hnr hL) htTr ht0.le (by positivity)
    have hd : 128 * ((t : ℝ) * Real.sqrt (K * n * L / t)) ≤
        128 * (Real.sqrt K * Real.sqrt (N * T * L)) := by
      rw [hd0]; linarith
    have expand : 8 * (t : ℝ) * (16 * K * ((K : ℝ) + 1) *
          (m / 2 + Real.sqrt (m * n * L / t) + 2 * n * L / (3 * t)) +
        16 * Real.sqrt (K * n * L / t)) =
        64 * (K * ((K : ℝ) + 1)) * (m * t) +
          128 * (K * ((K : ℝ) + 1)) * ((t : ℝ) * Real.sqrt (m * n * L / t)) +
          128 * (K * ((K : ℝ) + 1)) * ((t : ℝ) * (2 * n * L / (3 * t))) +
          128 * ((t : ℝ) * Real.sqrt (K * n * L / t)) := by ring
    rw [expand]
    have : 128 * (K : ℝ) ^ 2 * (epsBar * T) ≤ 130 * K ^ 2 * epsBar * T := by
      have : 0 ≤ (K : ℝ) ^ 2 * (epsBar * T) := by positivity
      nlinarith
    linarith

end OARsb

open OARsb in
theorem solution :
    ∃ C T1 : ℝ, ∀ (T N K : ℕ), T1 ≤ (T : ℝ) → 1 ≤ N → N ≤ T → 1 ≤ K →
      ∀ (epsBar : ℝ), 0 ≤ epsBar →
      ∀ (n : ℕ → ℕ), (∀ σ, n σ ≤ N) →
        4 * 1 * (epochLen N K T 0 : ℝ) +
            ∑ σ ∈ Finset.range (tau0 N K T),
              4 * deltaHat epsBar T K (epochLen N K T σ) (n σ) * (epochLen N K T (σ + 1) : ℝ) ≤
          C * (epsBar * K ^ 2 * T * Real.log T +
            (K ^ 2 * Real.sqrt epsBar + Real.sqrt K) * Real.sqrt (N * T * Real.log T ^ 3) +
            K ^ 2 * N * Real.log T ^ 2) := by
  refine ⟨2400, 3, ?_⟩
  intro T N K hT hN hNT hK epsBar he n hn
  have hTpos : (0 : ℝ) < T := by linarith
  have hlog1 : 1 ≤ Real.log (T : ℝ) := by
    rw [Real.le_log_iff_exp_le hTpos]
    have := Real.exp_one_lt_d9
    linarith
  set L := Real.log (T : ℝ) with hLdef
  have hL0 : 0 ≤ L := by linarith
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hT0 : 1 ≤ T0 N K T := by
    unfold T0
    apply Nat.one_le_iff_ne_zero.2
    apply Nat.pos_iff_ne_zero.1
    apply Nat.ceil_pos.2
    have : (0 : ℝ) < N := by linarith
    positivity
  -- the number of epochs
  have hstart : epochStart N K T (tau0 N K T) ≤ T - 1 := (epochOf_spec (T - 1)).1
  have hpow : (2 : ℝ) ^ (tau0 N K T) ≤ T := by
    have h1 := epochStart_add_T0 N K T (tau0 N K T)
    have h2 : 2 ^ (tau0 N K T) * T0 N K T ≤ T * T0 N K T := by
      have : T - 1 + T0 N K T ≤ T * T0 N K T := by
        rcases Nat.exists_eq_add_of_le hT0 with ⟨k, hk⟩
        have hT1 : 1 ≤ T := by exact_mod_cast (show (1 : ℝ) ≤ T by linarith)
        rw [hk]; rcases Nat.exists_eq_add_of_le hT1 with ⟨j, hj⟩; rw [hj]; ring_nf; omega
      omega
    have h3 : 2 ^ (tau0 N K T) ≤ T := Nat.le_of_mul_le_mul_right h2 (by omega)
    exact_mod_cast h3
  have htau : (tau0 N K T : ℝ) ≤ 2 * L := by
    have h1 : (tau0 N K T : ℝ) * Real.log 2 ≤ L := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) hpow
    have h2 := Real.log_two_gt_d9
    nlinarith
  -- each epoch before the last is shorter than T
  have hlen : ∀ σ ∈ Finset.range (tau0 N K T), epochLen N K T σ ≤ T := by
    intro σ hσ
    rw [Finset.mem_range] at hσ
    have h1 := epochStart_mono N K T (show σ + 1 ≤ tau0 N K T from hσ)
    rw [epochStart_succ] at h1
    omega
  set P : ℝ := 130 * K ^ 2 * epsBar * T + 256 * K ^ 2 * Real.sqrt epsBar * Real.sqrt (N * T * L) +
        171 * K ^ 2 * N * L + 128 * Real.sqrt K * Real.sqrt (N * T * L) with hP
  have hsum : ∑ σ ∈ Finset.range (tau0 N K T),
      4 * deltaHat epsBar T K (epochLen N K T σ) (n σ) * (epochLen N K T (σ + 1) : ℝ) ≤
      (tau0 N K T : ℝ) * P := by
    have : ∀ σ ∈ Finset.range (tau0 N K T),
        4 * deltaHat epsBar T K (epochLen N K T σ) (n σ) * (epochLen N K T (σ + 1) : ℝ) ≤ P := by
      intro σ hσ
      have e : (epochLen N K T (σ + 1) : ℝ) = 2 * epochLen N K T σ := by
        unfold epochLen; push_cast; ring
      rw [e]
      have := term_bound epsBar he T N K (epochLen N K T σ) (n σ) hK (epochLen_pos hT0 σ)
        (hlen σ hσ) (hn σ) hL0
      linarith
    calc _ ≤ ∑ _σ ∈ Finset.range (tau0 N K T), P := Finset.sum_le_sum this
      _ = _ := by simp
  have hP0 : 0 ≤ P := by positivity
  have hT0r : (T0 N K T : ℝ) ≤ 128 * ((K : ℝ) + 1) ^ 2 * N * L + 1 := by
    unfold T0
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hfirst : 4 * 1 * (epochLen N K T 0 : ℝ) ≤ 2052 * K ^ 2 * N * L ^ 2 := by
    have e : (epochLen N K T 0 : ℝ) = T0 N K T := by simp [epochLen]
    rw [e]
    have h1 : ((K : ℝ) + 1) ^ 2 ≤ 4 * K ^ 2 := by nlinarith
    have h2 : (1 : ℝ) ≤ K ^ 2 * N * L := by
      have : (1 : ℝ) ≤ K ^ 2 := one_le_pow₀ hKr
      have : (1 : ℝ) ≤ K ^ 2 * N := by nlinarith
      nlinarith
    have h3 : (K : ℝ) ^ 2 * N * L ≤ K ^ 2 * N * L ^ 2 := by
      have : 0 ≤ (K : ℝ) ^ 2 * N * L := by positivity
      nlinarith
    have h4 : 128 * ((K : ℝ) + 1) ^ 2 * N * L ≤ 512 * K ^ 2 * N * L := by
      have : 0 ≤ (N : ℝ) * L := by positivity
      nlinarith
    nlinarith
  have hsq : Real.sqrt (N * T * L) * L = Real.sqrt (N * T * L ^ 3) := by
    calc Real.sqrt (N * T * L) * L = Real.sqrt (N * T * L) * Real.sqrt (L ^ 2) := by
          rw [Real.sqrt_sq hL0]
      _ = Real.sqrt (N * T * L * L ^ 2) := (Real.sqrt_mul (by positivity) _).symm
      _ = _ := by congr 1; ring
  have htP : (tau0 N K T : ℝ) * P ≤ 2 * L * P := mul_le_mul_of_nonneg_right htau hP0
  have h2LP : 2 * L * P = 260 * (epsBar * K ^ 2 * T * L) +
      512 * (K ^ 2 * Real.sqrt epsBar) * (Real.sqrt (N * T * L) * L) +
      342 * (K ^ 2 * N * L ^ 2) + 256 * Real.sqrt K * (Real.sqrt (N * T * L) * L) := by
    rw [hP]; ring
  rw [hsq] at h2LP
  have a1 : 0 ≤ epsBar * K ^ 2 * T * L := by positivity
  have a2 : 0 ≤ K ^ 2 * Real.sqrt epsBar * Real.sqrt (N * T * L ^ 3) := by positivity
  have a3 : 0 ≤ Real.sqrt K * Real.sqrt (N * T * L ^ 3) := by positivity
  have a4 : 0 ≤ (K : ℝ) ^ 2 * N * L ^ 2 := by positivity
  have efin : 2400 * (epsBar * K ^ 2 * T * L +
      (K ^ 2 * Real.sqrt epsBar + Real.sqrt K) * Real.sqrt (N * T * L ^ 3) + K ^ 2 * N * L ^ 2) =
      2400 * (epsBar * K ^ 2 * T * L) + 2400 * (K ^ 2 * Real.sqrt epsBar * Real.sqrt (N * T * L ^ 3)) +
        2400 * (Real.sqrt K * Real.sqrt (N * T * L ^ 3)) + 2400 * (K ^ 2 * N * L ^ 2) := by ring
  rw [efin]
  have e2 : 512 * (K ^ 2 * Real.sqrt epsBar) * Real.sqrt (N * T * L ^ 3) =
      512 * (K ^ 2 * Real.sqrt epsBar * Real.sqrt (N * T * L ^ 3)) := by ring
  have e3 : 256 * Real.sqrt K * Real.sqrt (N * T * L ^ 3) =
      256 * (Real.sqrt K * Real.sqrt (N * T * L ^ 3)) := by ring
  have e4 : 2052 * (K : ℝ) ^ 2 * N * L ^ 2 = 2052 * (K ^ 2 * N * L ^ 2) := by ring
  linarith

-- Prove2me | solution 1 for TeleDriving.AmpleFleet.theorem_1C
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T10:07:36.911713+00:00
-- url     : https://prove2.me/submissions/fa205e46-3924-4e1a-aabb-82f7f9d485e6

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

set_option autoImplicit false

namespace TD1C

open TeleDriving.ScarceFleet

lemma weight_succ (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m j : ℕ) :
    weight mu lam m (j + 1) = weight mu lam m j * rho mu lam m ((j + 1 : ℕ) : ℝ) := by
  unfold weight
  rw [Finset.prod_Icc_succ_top (by omega)]

lemma weight_pos (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m : ℕ)
    (hρ : ∀ k : ℕ, 1 ≤ k → k ≤ m → 0 < rho mu lam m (k : ℝ)) (n : ℕ) (hn : n ≤ m) :
    0 < weight mu lam m n := by
  unfold weight
  apply Finset.prod_pos
  intro k hk
  have := Finset.mem_Icc.mp hk
  exact hρ k this.1 (by omega)

lemma W_succ (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m n : ℕ) :
    1 + ∑ i ∈ Finset.Icc 1 (n + 1), weight mu lam m i
      = (1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i) + weight mu lam m (n + 1) := by
  rw [Finset.sum_Icc_succ_top (by omega)]; ring

lemma W_pos (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m : ℕ)
    (hρ : ∀ k : ℕ, 1 ≤ k → k ≤ m → 0 < rho mu lam m (k : ℝ)) (n : ℕ) (hn : n ≤ m) :
    0 < 1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i := by
  have : 0 ≤ ∑ i ∈ Finset.Icc 1 n, weight mu lam m i := by
    apply Finset.sum_nonneg
    intro i hi
    have := Finset.mem_Icc.mp hi
    exact (weight_pos mu lam m hρ i (by omega)).le
  linarith

lemma SL_zero (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m : ℕ) : SL mu lam m 0 = 0 := by
  unfold SL piMN weight
  simp

lemma alg_SL (wn Wn g lam : ℝ) (hW : 0 < Wn) (hg : 0 < g) (hw : 0 ≤ wn) (hl : 0 ≤ lam) :
    (1 - wn * (lam / g) / (Wn + wn * (lam / g))) - (1 - wn / Wn)
      = wn / ((Wn + wn * (lam / g)) * g) * (g - lam * (1 - wn / Wn)) := by
  have h1 : 0 < Wn + wn * (lam / g) := by positivity
  field_simp
  ring

lemma alg_T (wn Wn g lam : ℝ) (hW : 0 < Wn) (hg : 0 < g) (hw : 0 ≤ wn) (hl : 0 ≤ lam) :
    lam * (1 - wn * (lam / g) / (Wn + wn * (lam / g))) - g
      = Wn / (Wn + wn * (lam / g)) * (lam * (1 - wn / Wn) - g) := by
  have h1 : 0 < Wn + wn * (lam / g) := by positivity
  field_simp
  ring

lemma step_SL (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m n : ℕ)
    (hρ : ∀ k : ℕ, 1 ≤ k → k ≤ m → 0 < rho mu lam m (k : ℝ)) (hn : n + 1 ≤ m)
    (hg : 0 < ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ)) (hl : 0 ≤ lam) :
    ∃ c > 0, SL mu lam m (n + 1) - SL mu lam m n
      = c * (((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ) - lam * SL mu lam m n) := by
  have hW := W_pos mu lam m hρ n (by omega)
  have hw := weight_pos mu lam m hρ n (by omega)
  have h1 : 0 < (1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i)
      + weight mu lam m n * (lam / (((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ))) := by
    positivity
  refine ⟨weight mu lam m n / (((1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i)
      + weight mu lam m n * (lam / (((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ))))
      * (((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ))), by positivity, ?_⟩
  unfold SL piMN
  rw [W_succ, weight_succ]
  unfold rho
  exact alg_SL _ _ _ _ hW hg hw.le hl

lemma step_T (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m n : ℕ)
    (hρ : ∀ k : ℕ, 1 ≤ k → k ≤ m → 0 < rho mu lam m (k : ℝ)) (hn : n + 1 ≤ m)
    (hg : 0 < ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ)) (hl : 0 ≤ lam) :
    ∃ d > 0, lam * SL mu lam m (n + 1) - ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ)
      = d * (lam * SL mu lam m n - ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ)) := by
  have hW := W_pos mu lam m hρ n (by omega)
  have hw := weight_pos mu lam m hρ n (by omega)
  have h1 : 0 < (1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i)
      + weight mu lam m n * (lam / (((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ))) := by
    positivity
  refine ⟨(1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i) / ((1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i)
      + weight mu lam m n * (lam / (((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ)))), by positivity, ?_⟩
  unfold SL piMN
  rw [W_succ, weight_succ]
  unfold rho
  exact alg_T _ _ _ _ hW hg hw.le hl

lemma weight_anti (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m K n : ℕ)
    (hw : ∀ j : ℕ, j ≤ n → 0 ≤ weight mu lam m j)
    (hle : ∀ k : ℕ, K < k → k ≤ n → rho mu lam m (k : ℝ) ≤ 1)
    (i : ℕ) (hi : K ≤ i) : ∀ d : ℕ, i + d ≤ n → weight mu lam m (i + d) ≤ weight mu lam m i := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro h
    have h1 := ih (by omega)
    rw [← add_assoc, weight_succ]
    have h2 := hle (i + d + 1) (by omega) (by omega)
    have h3 := hw (i + d) (by omega)
    calc weight mu lam m (i + d) * rho mu lam m ((i + d + 1 : ℕ) : ℝ)
        ≤ weight mu lam m (i + d) * 1 := mul_le_mul_of_nonneg_left h2 h3
      _ ≤ weight mu lam m i := by rw [mul_one]; exact h1

end TD1C

open TD1C in
open TeleDriving.ScarceFleet in
theorem solution (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : TeleDriving.ScarceFleet.Assumption1 mu s)
    (hA2 : TeleDriving.ScarceFleet.Assumption2 mu mbar) (hsize : TeleDriving.ScarceFleet.StandingSize mu s mbar m lam)
    (hreg : TeleDriving.ScarceFleet.IsSupplyRich mu lam m) (q3 : ℝ)
    (hq3 : q3 ∈ Set.Icc (1 : ℝ) m ∧ TeleDriving.ScarceFleet.rho mu lam m q3 = 1 ∧
      ∀ q ∈ Set.Icc (1 : ℝ) m, (TeleDriving.ScarceFleet.rho mu lam m q < 1 ↔ q3 < q)) :
    StrictMonoOn (TeleDriving.ScarceFleet.SL mu lam m) (Set.Icc 1 m) ∧
      ∀ n : ℕ, n ∈ Set.Icc 1 m → q3 < (n : ℝ) →
        1 - 1 / ((n : ℝ) - (⌊q3⌋₊ : ℝ)) < TeleDriving.ScarceFleet.SL mu lam m n := by
  classical
  obtain ⟨hs, hmupos, -, -, -, -, -⟩ := hA1
  obtain ⟨hmbar, hlam, -⟩ := hsize
  obtain ⟨-, hA2'⟩ := hA2
  obtain ⟨qhat, ⟨hq1, hqm⟩, hinc, hdec⟩ := hA2' m hmbar
  have hlam0 : 0 < lam := lt_trans (by positivity) hlam
  have hg : ∀ k : ℕ, 1 ≤ k → k ≤ m → 0 < (k : ℝ) * mu m (k : ℝ) := by
    intro k hk1 hkm
    have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have := hmupos m (k : ℝ) ⟨h1, by exact_mod_cast hkm⟩
    positivity
  have hρ : ∀ k : ℕ, 1 ≤ k → k ≤ m → 0 < rho mu lam m (k : ℝ) := by
    intro k hk1 hkm
    unfold rho
    exact div_pos hlam0 (hg k hk1 hkm)
  have sII : ∀ n : ℕ, n + 1 ≤ m →
      lam * SL mu lam m n < ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ) →
      SL mu lam m n < SL mu lam m (n + 1) := by
    intro n hn h
    obtain ⟨c, hc, he⟩ := step_SL mu lam m n hρ hn (hg (n + 1) (by omega) hn) hlam0.le
    have := mul_pos hc (sub_pos.2 h)
    linarith
  have INC : ∀ n : ℕ, n + 1 ≤ m → ((n + 1 : ℕ) : ℝ) ≤ qhat →
      lam * SL mu lam m n < ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ) := by
    intro n
    induction n with
    | zero =>
      intro h1 _
      have := hg 1 le_rfl h1
      simpa [SL_zero] using this
    | succ n ih =>
      intro h1 h2
      have hcast : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show n + 1 ≤ n + 1 + 1 by omega)
      have ih' := ih (by omega) (le_trans hcast h2)
      obtain ⟨d, hd, he⟩ := step_T mu lam m n hρ (by omega) (hg (n + 1) (by omega) (by omega))
        hlam0.le
      have hlt : lam * SL mu lam m (n + 1) < ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ) := by
        have := mul_pos hd (sub_pos.2 ih')
        nlinarith
      have hmono : ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ)
          < ((n + 1 + 1 : ℕ) : ℝ) * mu m ((n + 1 + 1 : ℕ) : ℝ) :=
        hinc ⟨by exact_mod_cast (show 1 ≤ n + 1 by omega), le_trans hcast h2⟩
          ⟨by exact_mod_cast (show 1 ≤ n + 1 + 1 by omega), h2⟩
          (by exact_mod_cast (show n + 1 < n + 1 + 1 by omega))
      linarith
  have SLlt : ∀ n : ℕ, n ≤ m → SL mu lam m n < 1 := by
    intro n hn
    have hw := weight_pos mu lam m hρ n hn
    have hW := W_pos mu lam m hρ n hn
    have : 0 < weight mu lam m n / (1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i) := div_pos hw hW
    unfold SL piMN
    linarith
  have KEY : ∀ n : ℕ, n + 1 ≤ m →
      lam * SL mu lam m n < ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ) := by
    intro n hn
    by_cases hq : ((n + 1 : ℕ) : ℝ) ≤ qhat
    · exact INC n hn hq
    · push Not at hq
      have hm' : ((n + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hn
      have h1 : (m : ℝ) * mu m (m : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ) :=
        hdec.antitoneOn ⟨hq.le, hm'⟩ ⟨hq.le.trans hm', le_rfl⟩ hm'
      have h2 : lam * SL mu lam m n < lam := by
        have := SLlt n (by omega)
        nlinarith
      have h3 : lam < (m : ℝ) * mu m (m : ℝ) := hreg
      linarith
  refine ⟨?_, ?_⟩
  · apply strictMonoOn_of_lt_succ Set.ordConnected_Icc
    intro a _ ha hb
    simp only [Order.succ_eq_add_one] at hb ⊢
    have hb' := Set.mem_Icc.mp hb
    exact sII a hb'.2 (KEY a hb'.2)
  · intro n hn hqn
    obtain ⟨hn1, hnm⟩ := Set.mem_Icc.mp hn
    obtain ⟨⟨hq31, hq3m⟩, -, hq3iff⟩ := hq3
    set K := ⌊q3⌋₊ with hKdef
    have hKq : (K : ℝ) ≤ q3 := Nat.floor_le (by linarith)
    have hKn : K < n := by exact_mod_cast (lt_of_le_of_lt hKq hqn)
    have hfl : q3 < (K : ℝ) + 1 := Nat.lt_floor_add_one q3
    have hle1 : ∀ k : ℕ, K < k → k ≤ n → rho mu lam m (k : ℝ) ≤ 1 := by
      intro k hk hkn
      have hk2 : ((K + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
      push_cast at hk2
      have hk' : q3 < (k : ℝ) := by linarith
      have hk1 : (1 : ℝ) ≤ k := by linarith
      exact ((hq3iff k ⟨hk1, by exact_mod_cast (le_trans hkn hnm)⟩).2 hk').le
    have hw : ∀ j : ℕ, j ≤ n → 0 ≤ weight mu lam m j :=
      fun j hj => (weight_pos mu lam m hρ j (by omega)).le
    have hS : ((n : ℝ) - K) * weight mu lam m n ≤ ∑ i ∈ Finset.Icc 1 n, weight mu lam m i := by
      have hsub : Finset.Icc (K + 1) n ⊆ Finset.Icc 1 n := Finset.Icc_subset_Icc_left (by omega)
      have h1 : ∑ i ∈ Finset.Icc (K + 1) n, weight mu lam m i
          ≤ ∑ i ∈ Finset.Icc 1 n, weight mu lam m i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hw i (Finset.mem_Icc.mp hi).2)
      have h2 : ∑ i ∈ Finset.Icc (K + 1) n, weight mu lam m n
          ≤ ∑ i ∈ Finset.Icc (K + 1) n, weight mu lam m i := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
        have := weight_anti mu lam m K n hw hle1 i (by omega) (n - i) (by omega)
        rwa [show i + (n - i) = n by omega] at this
      have h3 : ∑ i ∈ Finset.Icc (K + 1) n, weight mu lam m n
          = ((n : ℝ) - K) * weight mu lam m n := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        congr 1
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      linarith
    have hW := W_pos mu lam m hρ n hnm
    have hpos : (0 : ℝ) < (n : ℝ) - K := by
      have : ((K + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hKn
      push_cast at this
      linarith
    have hkey : weight mu lam m n / (1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i)
        < 1 / ((n : ℝ) - K) := by
      rw [div_lt_div_iff₀ hW hpos]
      nlinarith
    unfold SL piMN
    linarith

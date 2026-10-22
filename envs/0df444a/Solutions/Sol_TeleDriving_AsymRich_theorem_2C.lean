-- Prove2me | solution 1 for TeleDriving.AsymRich.theorem_2C
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T00:26:22.824278+00:00
-- url     : https://prove2.me/submissions/e420cd86-ca21-41ec-a28c-9953b1047b4e

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model
import Definitions.Def_TeleDriving_AsymRich_NStar

set_option autoImplicit false

namespace TD2C

open TeleDriving.ScarceFleet

lemma weight_succ (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m j : ℕ) :
    weight mu lam m (j + 1) = weight mu lam m j * rho mu lam m ((j + 1 : ℕ) : ℝ) := by
  unfold weight
  rw [Finset.prod_Icc_succ_top (by omega)]

lemma weight_nonneg (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m : ℕ)
    (hρ : ∀ k : ℕ, 1 ≤ k → 0 ≤ rho mu lam m (k : ℝ)) (i : ℕ) : 0 ≤ weight mu lam m i := by
  unfold weight
  apply Finset.prod_nonneg
  intro k hk
  exact hρ k (Finset.mem_Icc.mp hk).1

lemma weight_anti (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m K n : ℕ)
    (hρ : ∀ k : ℕ, 1 ≤ k → 0 ≤ rho mu lam m (k : ℝ))
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
    have h3 := weight_nonneg mu lam m hρ (i + d)
    calc weight mu lam m (i + d) * rho mu lam m ((i + d + 1 : ℕ) : ℝ)
        ≤ weight mu lam m (i + d) * 1 := mul_le_mul_of_nonneg_left h2 h3
      _ ≤ weight mu lam m i := by rw [mul_one]; exact h1

lemma piMN_nonneg (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m n q : ℕ)
    (hρ : ∀ k : ℕ, 1 ≤ k → 0 ≤ rho mu lam m (k : ℝ)) : 0 ≤ piMN mu lam m n q := by
  unfold piMN
  apply div_nonneg (weight_nonneg mu lam m hρ q)
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.Icc 1 n) => weight_nonneg mu lam m hρ i)
  linarith

lemma pi_bound (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m K n : ℕ) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hρ : ∀ k : ℕ, 1 ≤ k → 0 ≤ rho mu lam m (k : ℝ))
    (hle : ∀ k : ℕ, K < k → k ≤ n → rho mu lam m (k : ℝ) ≤ 1) :
    piMN mu lam m n n * ((n : ℝ) + 1 - K) ≤ 1 := by
  have hW : ∀ i, 0 ≤ weight mu lam m i := weight_nonneg mu lam m hρ
  have hS : ((n : ℝ) + 1 - K) * weight mu lam m n ≤ ∑ i ∈ Finset.Icc 1 n, weight mu lam m i := by
    have hsub : Finset.Icc K n ⊆ Finset.Icc 1 n := Finset.Icc_subset_Icc_left hK
    have h1 : ∑ i ∈ Finset.Icc K n, weight mu lam m i ≤ ∑ i ∈ Finset.Icc 1 n, weight mu lam m i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hW i)
    have h2 : ∑ i ∈ Finset.Icc K n, weight mu lam m n ≤ ∑ i ∈ Finset.Icc K n, weight mu lam m i := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
      have := weight_anti mu lam m K n hρ hle i hi1 (n - i) (by omega)
      rwa [show i + (n - i) = n by omega] at this
    have h3 : ∑ i ∈ Finset.Icc K n, weight mu lam m n = ((n : ℝ) + 1 - K) * weight mu lam m n := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      congr 1
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    linarith
  have hD : 0 ≤ ∑ i ∈ Finset.Icc 1 n, weight mu lam m i := Finset.sum_nonneg (fun i _ => hW i)
  unfold piMN
  rw [div_mul_eq_mul_div, div_le_one (by linarith)]
  linarith [mul_comm (weight mu lam m n) ((n : ℝ) + 1 - K)]

lemma rho_besbes_nonneg (s lam : ℝ) (m : ℕ) (k : ℝ) (hs : 0 < s) (hlam : 0 ≤ lam) (hk : 0 ≤ k) :
    0 ≤ rho (muBesbes s) lam m k := by
  unfold rho muBesbes
  apply div_nonneg hlam
  apply mul_nonneg hk
  apply div_nonneg zero_le_one
  exact add_nonneg (div_nonneg hs.le (Real.sqrt_nonneg _)) hs.le

lemma rho_besbes_le_one (s lam γ : ℝ) (m : ℕ) (k : ℝ) (hs : 0 < s) (hlam : 0 ≤ lam) (hγ : 0 < γ)
    (hk : (1 + γ) * (lam * s) ≤ k) (hk0 : 0 < k) (hr : 1 / γ ≤ Real.sqrt ((m : ℝ) - k + 1)) :
    rho (muBesbes s) lam m k ≤ 1 := by
  unfold rho muBesbes
  obtain ⟨r, hrdef⟩ : ∃ r, r = Real.sqrt ((m : ℝ) - k + 1) := ⟨_, rfl⟩
  rw [← hrdef] at hr ⊢
  have hr0 : 0 < r := lt_of_lt_of_le (one_div_pos.mpr hγ) hr
  have hrγ : 1 ≤ r * γ := (div_le_iff₀ hγ).mp hr
  have hsr : s / r ≤ s * γ := by
    rw [div_le_iff₀ hr0]
    nlinarith
  have hD : 0 < s / r + s := add_pos_of_nonneg_of_pos (div_nonneg hs.le hr0.le) hs
  rw [div_le_one (mul_pos hk0 (one_div_pos.mpr hD)), mul_one_div, le_div_iff₀ hD]
  nlinarith [mul_le_mul_of_nonneg_left hsr hlam]

end TD2C

open TeleDriving.ScarceFleet TeleDriving.AsymRich in
theorem solution (s alpha eps : ℝ) (hs : 0 < s) (ha : 2 < alpha) (heps : 0 < eps) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ lam in Filter.atTop,
      (nStar (TeleDriving.ScarceFleet.muBesbes s) lam eps (TeleDriving.ScarceFleet.mLam alpha s lam) : ℝ) / (TeleDriving.ScarceFleet.mLam alpha s lam : ℝ) ≤
        1 / alpha + δ := by
  intro δ hδ
  have ha0 : 0 < alpha := by linarith
  have hia : 0 < 1 / alpha := one_div_pos.mpr ha0
  have hinv : 1 / alpha < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) ha
  obtain ⟨d, hd0, hdδ, hdh⟩ : ∃ d : ℝ, 0 < d ∧ d ≤ δ ∧ d ≤ 1 / 2 - 1 / alpha :=
    ⟨min δ (1 / 2 - 1 / alpha), lt_min hδ (by linarith), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / alpha + d := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = alpha * d / 2 := ⟨_, rfl⟩
  have hc1 : c ≤ 1 / 2 := by linarith
  have hc0 : 0 < c := by linarith
  have hγ0 : 0 < γ := by rw [hγ]; positivity
  have hcid : ∀ x : ℝ, c * (alpha * x - 1) = x + 2 * γ * x - c := by
    intro x; rw [hc, hγ]; field_simp
  filter_upwards [Filter.eventually_gt_atTop ((1 / eps + c + 2) / (γ * s)),
    Filter.eventually_gt_atTop ((2 * (1 / γ) ^ 2 + 1) / (alpha * s)),
    Filter.eventually_gt_atTop 0] with lam h1 h2 hlam
  have h1' : 1 / eps + c + 2 < lam * (γ * s) := (div_lt_iff₀ (mul_pos hγ0 hs)).mp h1
  have h2' : 2 * (1 / γ) ^ 2 + 1 < lam * (alpha * s) := (div_lt_iff₀ (mul_pos ha0 hs)).mp h2
  have hls : 0 < lam * s := mul_pos hlam hs
  obtain ⟨m, hm⟩ : ∃ m, m = mLam alpha s lam := ⟨_, rfl⟩
  rw [← hm]
  have hmfl2 : alpha * lam * s < (m : ℝ) + 1 := by
    rw [hm]; unfold mLam; exact Nat.lt_floor_add_one _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊c * (m : ℝ)⌋₊ := ⟨_, rfl⟩
  have hn1 : (n : ℝ) ≤ c * m := by rw [hn]; exact Nat.floor_le (by positivity)
  have hn2 : c * m < (n : ℝ) + 1 := by rw [hn]; exact Nat.lt_floor_add_one _
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈(1 + γ) * (lam * s)⌉₊ := ⟨_, rfl⟩
  have hK1 : (1 + γ) * (lam * s) ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil _
  have hK2 : (K : ℝ) < (1 + γ) * (lam * s) + 1 := by
    rw [hK]; exact Nat.ceil_lt_add_one (by positivity)
  have hcm : c * (alpha * (lam * s) - 1) ≤ c * m :=
    mul_le_mul_of_nonneg_left (by nlinarith) hc0.le
  have hci := hcid (lam * s)
  have hieps : 0 < 1 / eps := one_div_pos.mpr heps
  have hgap : 1 / eps + 1 < (n : ℝ) + 1 - K := by nlinarith
  have hKn : K ≤ n := by
    have : (K : ℝ) < n + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  have hKpos : 1 ≤ K := by
    have : (0 : ℝ) < K := lt_of_lt_of_le (mul_pos (by linarith) hls) hK1
    exact_mod_cast this
  have hcm2 : c * m ≤ 1 / 2 * m := mul_le_mul_of_nonneg_right hc1 hm0
  have hnm : n ≤ m := by
    have : (n : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hmpos : (0 : ℝ) < m := by
    have : 1 ≤ m := le_trans hKpos (le_trans hKn hnm)
    exact_mod_cast this
  have hρ : ∀ k : ℕ, 1 ≤ k → 0 ≤ rho (muBesbes s) lam m (k : ℝ) :=
    fun k _ => TD2C.rho_besbes_nonneg s lam m k hs hlam.le (Nat.cast_nonneg _)
  have hle : ∀ k : ℕ, K < k → k ≤ n → rho (muBesbes s) lam m (k : ℝ) ≤ 1 := by
    intro k hk1 hk2
    have hk1' : (K : ℝ) < k := by exact_mod_cast hk1
    have hk2' : (k : ℝ) ≤ n := by exact_mod_cast hk2
    apply TD2C.rho_besbes_le_one s lam γ m k hs hlam.le hγ0 (by linarith) (by linarith)
    rw [show 1 / γ = Real.sqrt ((1 / γ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hpb := TD2C.pi_bound (muBesbes s) lam m K n hKpos hKn hρ hle
  have hpi0 := TD2C.piMN_nonneg (muBesbes s) lam m n n hρ
  have hpim := TD2C.piMN_nonneg (muBesbes s) lam m m m hρ
  have hpi : piMN (muBesbes s) lam m n n < eps := by
    by_contra hcon0
    have hcon := not_lt.mp hcon0
    have h := mul_le_mul hcon hgap.le (by linarith) hpi0
    have he : eps * (1 / eps + 1) = 1 + eps := by field_simp
    linarith
  have hmem : nStar (muBesbes s) lam eps m ≤ n := by
    unfold nStar
    apply Nat.sInf_le
    refine ⟨hKpos.trans hKn, hnm, ?_⟩
    unfold SL
    linarith
  have hns : (nStar (muBesbes s) lam eps m : ℝ) ≤ n := by exact_mod_cast hmem
  rw [div_le_iff₀ hmpos]
  have : c * m ≤ (1 / alpha + δ) * m := mul_le_mul_of_nonneg_right (by linarith) hm0
  linarith

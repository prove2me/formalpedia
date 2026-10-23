-- Prove2me | solution 1 for TeleDriving.AsymIntermediate.theorem_2B
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T13:30:14.642165+00:00
-- url     : https://prove2.me/submissions/cd3b1534-0a23-4114-bbf0-4ca3e9ba92d5

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

set_option autoImplicit false

namespace TD2B

open TeleDriving.ScarceFleet

lemma rho_eq (s lam : ℝ) (m k : ℕ) :
    rho (muBesbes s) lam m (k : ℝ) = lam * (s / Real.sqrt ((m : ℝ) - k + 1) + s) / k := by
  unfold rho muBesbes
  rw [mul_one_div, div_div_eq_mul_div]

lemma rho_pos (s lam : ℝ) (hs : 0 < s) (hl : 0 < lam) (m k : ℕ) (hk : 1 ≤ k) :
    0 < rho (muBesbes s) lam m (k : ℝ) := by
  rw [rho_eq]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : 0 < s / Real.sqrt ((m : ℝ) - k + 1) + s :=
    add_pos_of_nonneg_of_pos (div_nonneg hs.le (Real.sqrt_nonneg _)) hs
  exact div_pos (mul_pos hl h1) hk'

lemma rho_le (s lam b c : ℝ) (hs : 0 < s) (hl : 0 < lam) (hb : 0 < b) (hc0 : 0 ≤ c)
    (m k : ℕ) (hk : b * lam * s < k)
    (hc : s / Real.sqrt ((m : ℝ) - k + 1) ≤ c * s) :
    rho (muBesbes s) lam m (k : ℝ) ≤ (1 + c) / b := by
  rw [rho_eq]
  have hk' : (0 : ℝ) < k := lt_trans (by positivity) hk
  rw [div_le_div_iff₀ hk' hb]
  have h1 : lam * (s / Real.sqrt ((m : ℝ) - k + 1)) ≤ lam * (c * s) :=
    mul_le_mul_of_nonneg_left hc hl.le
  have h2 : b * (lam * (s / Real.sqrt ((m : ℝ) - k + 1))) ≤ b * (lam * (c * s)) :=
    mul_le_mul_of_nonneg_left h1 hb.le
  have h3 : (1 + c) * (b * lam * s) ≤ (1 + c) * k :=
    mul_le_mul_of_nonneg_left hk.le (by linarith)
  nlinarith [h2, h3]

lemma weight_nonneg (s lam : ℝ) (hs : 0 < s) (hl : 0 < lam) (m i : ℕ) :
    0 ≤ weight (muBesbes s) lam m i := by
  unfold weight
  apply Finset.prod_nonneg
  intro k hk
  exact (rho_pos s lam hs hl m k (Finset.mem_Icc.mp hk).1).le

lemma weight_pos (s lam : ℝ) (hs : 0 < s) (hl : 0 < lam) (m i : ℕ) :
    0 < weight (muBesbes s) lam m i := by
  unfold weight
  apply Finset.prod_pos
  intro k hk
  exact rho_pos s lam hs hl m k (Finset.mem_Icc.mp hk).1

lemma weight_split (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m K n : ℕ) (hK : K ≤ n) :
    weight mu lam m n = weight mu lam m K * ∏ k ∈ Finset.Ioc K n, rho mu lam m (k : ℝ) := by
  unfold weight
  have e : ∀ j : ℕ, Finset.Icc 1 j = Finset.Ioc 0 j := by
    intro j; ext x; simp [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [e n, e K]
  exact (Finset.prod_Ioc_consecutive _ (Nat.zero_le K) hK).symm

lemma piMN_nonneg (s lam : ℝ) (hs : 0 < s) (hl : 0 < lam) (m n q : ℕ) :
    0 ≤ piMN (muBesbes s) lam m n q := by
  unfold piMN
  apply div_nonneg (weight_nonneg s lam hs hl m q)
  have : 0 ≤ ∑ i ∈ Finset.Icc 1 n, weight (muBesbes s) lam m i :=
    Finset.sum_nonneg fun i _ => weight_nonneg s lam hs hl m i
  linarith

lemma SL_le_one (s lam : ℝ) (hs : 0 < s) (hl : 0 < lam) (m n : ℕ) :
    SL (muBesbes s) lam m n ≤ 1 := by
  unfold SL
  linarith [piMN_nonneg s lam hs hl m n n]

lemma pi_le_prod (s lam : ℝ) (hs : 0 < s) (hl : 0 < lam) (m K : ℕ) (hK1 : 1 ≤ K) (hKm : K ≤ m) :
    piMN (muBesbes s) lam m m m ≤ ∏ k ∈ Finset.Ioc K m, rho (muBesbes s) lam m (k : ℝ) := by
  unfold piMN
  have hWK := weight_pos s lam hs hl m K
  have hsum : weight (muBesbes s) lam m K ≤ 1 + ∑ i ∈ Finset.Icc 1 m, weight (muBesbes s) lam m i := by
    have := Finset.single_le_sum (f := fun i => weight (muBesbes s) lam m i)
      (fun i _ => weight_nonneg s lam hs hl m i) (Finset.mem_Icc.mpr ⟨hK1, hKm⟩)
    linarith
  calc weight (muBesbes s) lam m m / (1 + ∑ i ∈ Finset.Icc 1 m, weight (muBesbes s) lam m i)
      ≤ weight (muBesbes s) lam m m / weight (muBesbes s) lam m K :=
        div_le_div_of_nonneg_left (weight_nonneg s lam hs hl m m) hWK hsum
    _ = ∏ k ∈ Finset.Ioc K m, rho (muBesbes s) lam m (k : ℝ) := by
        rw [weight_split (muBesbes s) lam m K m hKm, mul_div_cancel_left₀ _ hWK.ne']

lemma pi_bound (s lam b δ : ℝ) (hs : 0 < s) (hl : 0 < lam) (hb : 0 < b) (hδ : 0 < δ)
    (m K C : ℕ) (hK1 : 1 ≤ K) (hKC : K + C ≤ m)
    (hKb : ∀ k : ℕ, K < k → b * lam * s < k)
    (hC : (1 / δ) ^ 2 ≤ (C : ℝ) + 1) :
    piMN (muBesbes s) lam m m m ≤ ((1 + δ) / b) ^ (m - C - K) * ((1 + 1) / b) ^ C := by
  refine le_trans (pi_le_prod s lam hs hl m K hK1 (by omega)) ?_
  have hsplit := Finset.prod_Ioc_consecutive (fun k : ℕ => rho (muBesbes s) lam m (k : ℝ))
    (show K ≤ m - C by omega) (show m - C ≤ m by omega)
  rw [← hsplit]
  have hρ0 : ∀ k : ℕ, K < k → 0 ≤ rho (muBesbes s) lam m (k : ℝ) :=
    fun k hk => (rho_pos s lam hs hl m k (by omega)).le
  have P1 : ∏ k ∈ Finset.Ioc K (m - C), rho (muBesbes s) lam m (k : ℝ)
      ≤ ((1 + δ) / b) ^ (m - C - K) := by
    have := Finset.prod_le_prod (s := Finset.Ioc K (m - C))
      (f := fun k : ℕ => rho (muBesbes s) lam m (k : ℝ)) (g := fun _ => (1 + δ) / b)
      (fun k hk => hρ0 k (Finset.mem_Ioc.mp hk).1) ?_
    · simp only [Finset.prod_const, Nat.card_Ioc] at this; exact this
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ioc.mp hk
    apply rho_le s lam b δ hs hl hb hδ.le m k (hKb k hk1)
    have hkC : k + C ≤ m := by omega
    have hkC' : (k : ℝ) + C ≤ m := by exact_mod_cast hkC
    have hsq : 1 / δ ≤ Real.sqrt ((m : ℝ) - k + 1) := by
      rw [Real.le_sqrt (by positivity)]
      all_goals linarith
    have hpos : 0 < 1 / δ := by positivity
    calc s / Real.sqrt ((m : ℝ) - k + 1) ≤ s / (1 / δ) :=
          div_le_div_of_nonneg_left hs.le hpos hsq
      _ = δ * s := by field_simp
  have P2 : ∏ k ∈ Finset.Ioc (m - C) m, rho (muBesbes s) lam m (k : ℝ)
      ≤ ((1 + 1) / b) ^ C := by
    have := Finset.prod_le_prod (s := Finset.Ioc (m - C) m)
      (f := fun k : ℕ => rho (muBesbes s) lam m (k : ℝ)) (g := fun _ => (1 + 1) / b)
      (fun k hk => hρ0 k (by have := (Finset.mem_Ioc.mp hk).1; omega)) ?_
    · have hc : m - (m - C) = C := by omega
      simp only [Finset.prod_const, Nat.card_Ioc, hc] at this; exact this
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ioc.mp hk
    apply rho_le s lam b 1 hs hl hb zero_le_one m k (hKb k (by omega))
    have hk2' : (k : ℝ) ≤ m := by exact_mod_cast hk2
    have hsq : 1 ≤ Real.sqrt ((m : ℝ) - k + 1) := by
      rw [Real.le_sqrt zero_le_one]
      all_goals linarith
    calc s / Real.sqrt ((m : ℝ) - k + 1) ≤ s / 1 :=
          div_le_div_of_nonneg_left hs.le one_pos hsq
      _ = 1 * s := by ring
  apply mul_le_mul P1 P2
  · exact Finset.prod_nonneg fun k hk => hρ0 k (by have := (Finset.mem_Ioc.mp hk).1; omega)
  · exact pow_nonneg (by positivity) _

lemma ratio_bounds (s lam : ℝ) (hs : 0 < s) (hl : 0 < lam) (m : ℕ) (hm : 1 ≤ m)
    (hSL : 0 < SL (muBesbes s) lam m m) :
    1 ≤ maxSLRatio (muBesbes s) lam m ∧
      maxSLRatio (muBesbes s) lam m ≤ 1 / SL (muBesbes s) lam m m := by
  unfold maxSLRatio
  constructor
  · have h := le_ciSup (Set.finite_range
      (fun n : Fin m => SL (muBesbes s) lam m ((n : ℕ) + 1) / SL (muBesbes s) lam m m)).bddAbove
      ⟨m - 1, by omega⟩
    have e : m - 1 + 1 = m := by omega
    simp only [e, div_self hSL.ne'] at h
    exact h
  · have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    apply ciSup_le
    intro n
    exact div_le_div_of_nonneg_right (SL_le_one s lam hs hl m _) hSL.le

end TD2B

open TeleDriving.ScarceFleet in
theorem solution (s alpha : ℝ) (hs : 0 < s) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    Filter.Tendsto (fun lam : ℝ => TeleDriving.ScarceFleet.maxSLRatio (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam))
      Filter.atTop (nhds 1) := by
  set b : ℝ := (1 + alpha) / 2 with hbdef
  set δ : ℝ := (alpha - 1) / 4 with hδdef
  have hb : 0 < b := by rw [hbdef]; linarith
  have hb1 : 1 < b := by rw [hbdef]; linarith
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hab : 0 < alpha - b := by rw [hbdef]; linarith
  set C : ℕ := ⌈(1 / δ) ^ 2⌉₊ with hCdef
  have hC : (1 / δ) ^ 2 ≤ (C : ℝ) + 1 := by
    have := Nat.le_ceil ((1 / δ) ^ 2); linarith
  set r : ℝ := (1 + δ) / b with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hrdef, div_lt_one hb, hbdef, hδdef]; linarith
  let K : ℝ → ℕ := fun lam => ⌊b * lam * s⌋₊
  let N : ℝ → ℕ := fun lam => mLam alpha s lam - C - K lam
  -- N tends to infinity
  have hN : Filter.Tendsto N Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro B
    have hden : 0 < (alpha - b) * s := mul_pos hab hs
    filter_upwards [Filter.eventually_ge_atTop (((B : ℝ) + C + 2) / ((alpha - b) * s))] with lam hlam
    have hlam' : (B : ℝ) + C + 2 ≤ (alpha - b) * s * lam := by
      rw [div_le_iff₀ hden] at hlam; linarith
    have hl0 : 0 < lam := by
      have h0 : (0 : ℝ) < (B : ℝ) + C + 2 := by positivity
      have : 0 < (alpha - b) * s * lam := by linarith
      exact pos_of_mul_pos_right this hden.le
    have hm : alpha * lam * s - 1 < (mLam alpha s lam : ℝ) := by
      unfold mLam
      have := Nat.lt_floor_add_one (alpha * lam * s); linarith
    have hK : (K lam : ℝ) ≤ b * lam * s :=
      Nat.floor_le (by have := mul_pos (mul_pos hb hl0) hs; linarith)
    have hreal : (K lam : ℝ) + C + B < mLam alpha s lam := by nlinarith
    have hnat : K lam + C + B < mLam alpha s lam := by exact_mod_cast hreal
    show B ≤ mLam alpha s lam - C - K lam
    omega
  -- the bound tends to zero
  have hf : Filter.Tendsto (fun lam => r ^ (N lam) * ((1 + 1) / b) ^ C) Filter.atTop (nhds 0) := by
    have h1 := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp hN).mul_const (((1 + 1) / b) ^ C)
    simpa using h1
  have hpos : ∀ᶠ lam : ℝ in Filter.atTop, 0 < lam := Filter.eventually_gt_atTop 0
  have hK1 : ∀ᶠ lam : ℝ in Filter.atTop, 1 ≤ K lam := by
    filter_upwards [Filter.eventually_ge_atTop (1 / (b * s))] with lam hlam
    have hbs : 0 < b * s := mul_pos hb hs
    have : 1 ≤ b * lam * s := by
      rw [div_le_iff₀ hbs] at hlam; nlinarith
    exact Nat.le_floor (by simpa using this)
  have hN1 : ∀ᶠ lam : ℝ in Filter.atTop, 1 ≤ N lam := hN.eventually_ge_atTop 1
  -- pi tends to zero
  have hpi : Filter.Tendsto (fun lam => piMN (muBesbes s) lam (mLam alpha s lam) (mLam alpha s lam)
      (mLam alpha s lam)) Filter.atTop (nhds 0) := by
    apply squeeze_zero' _ _ hf
    · filter_upwards [hpos] with lam hl
      exact TD2B.piMN_nonneg s lam hs hl _ _ _
    · filter_upwards [hpos, hK1, hN1] with lam hl hk1 hn1
      have hKC : K lam + C ≤ mLam alpha s lam := by
        have : 1 ≤ mLam alpha s lam - C - K lam := hn1
        omega
      have hKb : ∀ k : ℕ, K lam < k → b * lam * s < k := by
        intro k hk
        have h1 := Nat.lt_floor_add_one (b * lam * s)
        have h2 : (K lam : ℝ) + 1 ≤ k := by exact_mod_cast hk
        show b * lam * s < k
        linarith
      exact TD2B.pi_bound s lam b δ hs hl hb hδ (mLam alpha s lam) (K lam) C hk1 hKC hKb hC
  have hSL : Filter.Tendsto (fun lam => SL (muBesbes s) lam (mLam alpha s lam) (mLam alpha s lam))
      Filter.atTop (nhds 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub hpi
    simpa [SL] using this
  have hSLpos : ∀ᶠ lam : ℝ in Filter.atTop,
      0 < SL (muBesbes s) lam (mLam alpha s lam) (mLam alpha s lam) :=
    hSL.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hinv : Filter.Tendsto (fun lam => 1 / SL (muBesbes s) lam (mLam alpha s lam) (mLam alpha s lam))
      Filter.atTop (nhds 1) := by
    have := hSL.inv₀ one_ne_zero
    simpa using this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
  · filter_upwards [hpos, hK1, hN1, hSLpos] with lam hl hk1 hn1 hsl
    have hm : 1 ≤ mLam alpha s lam := by
      have : 1 ≤ mLam alpha s lam - C - K lam := hn1
      omega
    exact (TD2B.ratio_bounds s lam hs hl _ hm hsl).1
  · filter_upwards [hpos, hK1, hN1, hSLpos] with lam hl hk1 hn1 hsl
    have hm : 1 ≤ mLam alpha s lam := by
      have : 1 ≤ mLam alpha s lam - C - K lam := hn1
      omega
    exact (TD2B.ratio_bounds s lam hs hl _ hm hsl).2

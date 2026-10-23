-- Prove2me | solution 1 for PostTradeFees.Welfare.corollary_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T04:47:28.40098+00:00
-- url     : https://prove2.me/submissions/263d7e45-e186-4ab7-a87b-fd3cf406fad3

import Mathlib
import Definitions.Def_PostTradeFees_Welfare_Model

set_option autoImplicit false

namespace PTF5d

open PostTradeFees.Welfare

open Classical in
lemma stat_eqs {N : ℕ} {p q : Prop} {φ : Fin 3 → ℝ}
    (h : MarkovChain.IsStationary (chain N p q) φ) :
    φ 0 + φ 1 + φ 2 = 1 ∧
    φ 1 = φ 0 * (if p then 1 / (2 * (N:ℝ)) else 0) ∧
    φ 2 = φ 0 * (if q then ((N:ℝ) - 1) / (2 * (N:ℝ)) else 0) := by
  obtain ⟨hs, hv⟩ := h
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  have hsum : ∑ i, φ i = 1 := hs.2
  rw [Fin.sum_univ_three] at hsum
  simp [chain, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at h1 h2
  refine ⟨hsum, ?_, ?_⟩
  · rw [← h1]; split_ifs <;> ring
  · rw [← h2]; split_ifs <;> ring

/-- abstract one-sided profit under trade-specific fees -/
noncomputable def hTS (n c x u : ℝ) : ℝ :=
  1 / 2 * (1 / n * (if 0 ≤ u then x - u else 0) +
    (n - 1) / n * (if c ≤ u then x - u - c else 0))

lemma hTS_zero (n c x : ℝ) (hn : 1 < n) (hc : 0 < c) :
    2 * n * hTS n c x 0 = x := by
  have hn0 : n ≠ 0 := by linarith
  simp [hTS, not_le.mpr hc]
  field_simp

lemma hTS_ge (n c k x u : ℝ) (hn : 1 < n) (hc : 0 < c) (hk : 2 * n * k = c * (2 * n - 1))
    (hu : c ≤ u) : 2 * hTS n c x u = x - 2 * k - (u - c) := by
  have hn0 : n ≠ 0 := by linarith
  have h0 : 0 ≤ u := by linarith
  simp only [hTS, if_pos h0, if_pos hu]
  have : k = c * (2 * n - 1) / (2 * n) := by field_simp; linarith
  rw [this]
  field_simp
  ring

lemma hTS_mid (n c x u : ℝ) (hn : 1 < n) (h0 : 0 ≤ u) (hu : ¬ c ≤ u) :
    2 * n * hTS n c x u = x - u := by
  have hn0 : n ≠ 0 := by linarith
  simp only [hTS, if_pos h0, if_neg hu]
  field_simp
  ring

lemma hTS_neg (n c x u : ℝ) (hc : 0 < c) (h0 : ¬ 0 ≤ u) : hTS n c x u = 0 := by
  have hu : ¬ c ≤ u := fun h => h0 (by linarith)
  simp [hTS, if_neg h0, if_neg hu]

lemma sideTS (n c k x V : ℝ) (hn : 1 < n) (hc : 0 < c) (hk : 2 * n * k = c * (2 * n - 1))
    (hmem : ∃ u, hTS n c x u = V) (hub : ∀ u, hTS n c x u ≤ V) :
    x ≤ 2 * n * V ∧ x - 2 * k ≤ 2 * V ∧ 0 ≤ V ∧
      (2 * n * V = x ∨ 2 * V = x - 2 * k ∨ V = 0) := by
  have hn0 : 0 < n := by linarith
  have e0 := hTS_zero n c x hn hc
  have ec := hTS_ge n c k x c hn hc hk le_rfl
  have en := hTS_neg n c x (-1) hc (by norm_num)
  have b0 := hub 0
  have bc := hub c
  have bn := hub (-1)
  have i1 : x ≤ 2 * n * V := by nlinarith
  have i2 : x - 2 * k ≤ 2 * V := by linarith
  have i3 : 0 ≤ V := by linarith
  refine ⟨i1, i2, i3, ?_⟩
  obtain ⟨u, rfl⟩ := hmem
  by_cases h0 : 0 ≤ u
  · by_cases hcu : c ≤ u
    · right; left
      have := hTS_ge n c k x u hn hc hk hcu
      linarith
    · left
      have := hTS_mid n c x u hn h0 hcu
      nlinarith
  · right; right
    exact hTS_neg n c x u hc h0

lemma caseOA (n D k Vb Vs : ℝ) (hn : 1 < n)
    (hb : 2 * n * Vb = D - Vs) (ha : 2 * Vs = D - Vb - 2 * k)
    (A1 : D - Vb ≤ 2 * n * Vs) (B2 : D - Vs - 2 * k ≤ 2 * Vb) :
    2 * Vb = D - Vs - 2 * k ∧ k * (2 * n + 1) = (n - 1) * D := by
  have hn0 : 0 < n := by linarith
  have m1 : n * (2 * Vs) = n * (D - Vb - 2 * k) := by rw [ha]
  have s1 : 0 ≤ (2 * n - 1) * (Vs - Vb) := by linarith
  have hVs : Vb ≤ Vs := by
    have := (mul_nonneg_iff_of_pos_left (by linarith : (0:ℝ) < 2 * n - 1)).mp s1
    linarith
  have t1 : n * (D - Vs - 2 * k) ≤ n * (2 * Vb) := mul_le_mul_of_nonneg_left B2 hn0.le
  have t2 : n * Vs ≤ n * Vb := by linarith
  have hVb : Vs ≤ Vb := le_of_mul_le_mul_left t2 hn0
  have hE : Vb = Vs := le_antisymm hVs hVb
  subst hE
  constructor
  · linarith
  · linarith

lemma coreTS (n D k Vb Vs : ℝ) (hn : 1 < n) (hD : 0 < D) (hk0 : 0 < k)
    (B1 : D - Vs ≤ 2 * n * Vb) (B2 : D - Vs - 2 * k ≤ 2 * Vb) (B3 : 0 ≤ Vb)
    (B4 : 2 * n * Vb = D - Vs ∨ 2 * Vb = D - Vs - 2 * k ∨ Vb = 0)
    (A1 : D - Vb ≤ 2 * n * Vs) (A2 : D - Vb - 2 * k ≤ 2 * Vs) (A3 : 0 ≤ Vs)
    (A4 : 2 * n * Vs = D - Vb ∨ 2 * Vs = D - Vb - 2 * k ∨ Vs = 0) :
    (k * (2 * n + 1) ≤ (n - 1) * D → 2 * Vb = D - Vs - 2 * k ∧ 2 * Vs = D - Vb - 2 * k) ∧
    ((n - 1) * D < k * (2 * n + 1) → 2 * n * Vb = D - Vs ∧ D - Vs - 2 * k < 2 * Vb ∧
      2 * n * Vs = D - Vb ∧ D - Vb - 2 * k < 2 * Vs) := by
  have hn0 : 0 < n := by linarith
  have hnD : D < n * D := by nlinarith
  have hVsD : Vs < D := by
    rcases A4 with h | h | h
    · by_contra hc; rw [not_lt] at hc; nlinarith
    · linarith
    · linarith
  have hVbD : Vb < D := by
    rcases B4 with h | h | h
    · by_contra hc; rw [not_lt] at hc; nlinarith
    · linarith
    · linarith
  have h2n : (0:ℝ) < 2 * n + 1 := by linarith
  rcases B4 with hb | hb | hb
  · rcases A4 with ha | ha | ha
    · -- own / own
      have e : (2 * n - 1) * (Vb - Vs) = 0 := by linarith
      have hE : Vb = Vs := by
        rcases mul_eq_zero.mp e with h | h
        · linarith
        · linarith
      subst hE
      constructor
      · intro hR
        have h1 : (2 * n + 1) * (3 * Vb + 2 * k - D) ≤ (2 * n + 1) * 0 := by linarith
        have := le_of_mul_le_mul_left h1 h2n
        constructor <;> linarith
      · intro hR
        have h1 : (2 * n + 1) * 0 < (2 * n + 1) * (3 * Vb + 2 * k - D) := by linarith
        have := lt_of_mul_lt_mul_left h1 h2n.le
        refine ⟨hb, by linarith, ha, by linarith⟩
    · -- bid own / ask all
      obtain ⟨e1, e2⟩ := caseOA n D k Vb Vs hn hb ha A1 B2
      constructor
      · intro _; exact ⟨e1, ha⟩
      · intro hR; linarith
    · subst ha; linarith
  · rcases A4 with ha | ha | ha
    · -- bid all / ask own
      obtain ⟨e1, e2⟩ := caseOA n D k Vs Vb hn ha hb B1 A2
      constructor
      · intro _; exact ⟨hb, e1⟩
      · intro hR; linarith
    · -- all / all
      have hE : Vb = Vs := by linarith
      subst hE
      constructor
      · intro _; exact ⟨hb, ha⟩
      · intro hR
        have h3 : 3 * Vb = D - 2 * k := by linarith
        have m : n * (3 * Vb) = n * (D - 2 * k) := by rw [h3]
        linarith
    · subst ha; linarith
  · subst hb; linarith

lemma fee_ts_t (P : Params) : fee P .tradeSpecific true = 0 := rfl
lemma fee_ts_f (P : Params) : fee P .tradeSpecific false = P.c := rfl
lemma fee_u (P : Params) (b : Bool) : fee P .uniform b = ((P.N : ℝ) - 1) / (P.N : ℝ) * P.c := by
  cases b <;> rfl

lemma bidTS (P : Params) (Vs B : ℝ) :
    bidProfit P .tradeSpecific Vs B =
      hTS (P.N : ℝ) P.c (P.Vh - P.Vl - Vs) (B - P.Vl - Vs) := by
  unfold bidProfit hTS
  rw [fee_ts_t, fee_ts_f]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 <;>
    simp only [SellerHits, fee_ts_t, fee_ts_f] at * <;>
    first | (exfalso; linarith) | ring1

lemma askTS (P : Params) (Vb A : ℝ) :
    askProfit P .tradeSpecific Vb A =
      hTS (P.N : ℝ) P.c (P.Vh - P.Vl - Vb) (P.Vh - A - Vb) := by
  unfold askProfit hTS
  rw [fee_ts_t, fee_ts_f]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 <;>
    simp only [BuyerHits, fee_ts_t, fee_ts_f] at * <;>
    first | (exfalso; linarith) | ring1

noncomputable def hU (x u : ℝ) : ℝ := 1 / 2 * (if 0 ≤ u then x - u else 0)

lemma bidU (P : Params) (hN : (0 : ℝ) < P.N) (Vs B : ℝ) :
    bidProfit P .uniform Vs B =
      hU (P.Vh - P.Vl - 2 * (((P.N : ℝ) - 1) / (P.N : ℝ) * P.c) - Vs)
        (B - P.Vl - ((P.N : ℝ) - 1) / (P.N : ℝ) * P.c - Vs) := by
  unfold bidProfit hU
  rw [fee_u, fee_u]
  split_ifs with h1 h2 h3 h4 h5 h6 <;>
    simp only [SellerHits, fee_u] at * <;>
    first | (exfalso; linarith) | ring1 | (field_simp; ring1)

lemma askU (P : Params) (hN : (0 : ℝ) < P.N) (Vb A : ℝ) :
    askProfit P .uniform Vb A =
      hU (P.Vh - P.Vl - 2 * (((P.N : ℝ) - 1) / (P.N : ℝ) * P.c) - Vb)
        (P.Vh - A - ((P.N : ℝ) - 1) / (P.N : ℝ) * P.c - Vb) := by
  unfold askProfit hU
  rw [fee_u, fee_u]
  split_ifs with h1 h2 h3 h4 h5 h6 <;>
    simp only [BuyerHits, fee_u] at * <;>
    first | (exfalso; linarith) | ring1 | (field_simp; ring1)

lemma sideU (x V : ℝ) (hmem : ∃ u, hU x u = V) (hub : ∀ u, hU x u ≤ V) :
    x ≤ 2 * V ∧ 0 ≤ V ∧ (2 * V = x ∨ V = 0) := by
  have b0 := hub 0
  have bn := hub (-1)
  simp only [hU, le_refl, if_true] at b0
  simp only [hU, show ¬ (0:ℝ) ≤ -1 by norm_num, if_false] at bn
  refine ⟨by linarith, by linarith, ?_⟩
  obtain ⟨u, rfl⟩ := hmem
  unfold hU at b0 bn ⊢
  by_cases h : 0 ≤ u
  · left; simp only [h, if_true] at b0 ⊢; linarith
  · right; simp [h]

lemma coreU (K Vb Vs : ℝ) (hK : 0 < K)
    (B1 : K - Vs ≤ 2 * Vb) (B3 : 0 ≤ Vb) (B4 : 2 * Vb = K - Vs ∨ Vb = 0)
    (A1 : K - Vb ≤ 2 * Vs) (A3 : 0 ≤ Vs) (A4 : 2 * Vs = K - Vb ∨ Vs = 0) :
    2 * Vb = K - Vs ∧ 2 * Vs = K - Vb := by
  rcases B4 with hb | hb <;> rcases A4 with ha | ha
  · exact ⟨hb, ha⟩
  · subst ha; constructor <;> linarith
  · subst hb; constructor <;> linarith
  · subst hb; subst ha; constructor <;> linarith

lemma w_all (P : Params) (hn : (1 : ℝ) < P.N) {p q : Prop} (hp : p) (hq : q) {φ : Fin 3 → ℝ}
    (h : MarkovChain.IsStationary (chain P.N p q) φ) :
    welfare P φ = (P.Vh - P.Vl) / 3 - 2 * P.c * ((P.N : ℝ) - 1) / (3 * (P.N : ℝ)) := by
  obtain ⟨hs, h1, h2⟩ := stat_eqs h
  rw [if_pos hp] at h1
  rw [if_pos hq] at h2
  have hn0 : (P.N : ℝ) ≠ 0 := by linarith
  have k : φ 0 * (1 / (2 * (P.N : ℝ))) + φ 0 * (((P.N : ℝ) - 1) / (2 * (P.N : ℝ))) = φ 0 / 2 := by
    field_simp; ring
  have h0 : φ 0 = 2 / 3 := by linarith
  unfold welfare
  rw [h1, h2, h0]
  field_simp
  ring

lemma w_own (P : Params) (hn : (1 : ℝ) < P.N) {p q : Prop} (hp : p) (hq : ¬ q) {φ : Fin 3 → ℝ}
    (h : MarkovChain.IsStationary (chain P.N p q) φ) :
    welfare P φ = (P.Vh - P.Vl) / (2 * (P.N : ℝ) + 1) := by
  obtain ⟨hs, h1, h2⟩ := stat_eqs h
  rw [if_pos hp] at h1
  rw [if_neg hq] at h2
  have hn0 : (P.N : ℝ) ≠ 0 := by linarith
  have hn1 : (2 * (P.N : ℝ) + 1) ≠ 0 := by linarith
  have h0 : φ 0 = 2 * (P.N : ℝ) / (2 * (P.N : ℝ) + 1) := by
    rw [h1, h2] at hs
    field_simp
    field_simp at hs
    linarith
  unfold welfare
  rw [h1, h2, h0]
  field_simp
  ring

lemma w_none (P : Params) {p q : Prop} (hp : ¬ p) (hq : ¬ q) {φ : Fin 3 → ℝ}
    (h : MarkovChain.IsStationary (chain P.N p q) φ) :
    welfare P φ = 0 := by
  obtain ⟨hs, h1, h2⟩ := stat_eqs h
  rw [if_neg hp] at h1
  rw [if_neg hq] at h2
  unfold welfare
  rw [h1, h2]
  ring

lemma wdiff (P : Params) (hn : (1 : ℝ) < P.N) :
    ((P.Vh - P.Vl) / 3 - 2 * P.c * ((P.N : ℝ) - 1) / (3 * (P.N : ℝ))) -
      (P.Vh - P.Vl) / (2 * (P.N : ℝ) + 1) =
    2 * ((P.N : ℝ) - 1) / (3 * (P.N : ℝ)) * (c2 P - P.c) := by
  have hn0 : (P.N : ℝ) ≠ 0 := by linarith
  have hn1 : (2 * (P.N : ℝ) + 1) ≠ 0 := by linarith
  unfold c2
  field_simp
  ring

lemma reg_id (P : Params) (hn : (1 : ℝ) < P.N) :
    P.c * (2 * (P.N : ℝ) - 1) / (2 * (P.N : ℝ)) * (2 * (P.N : ℝ) + 1) - ((P.N : ℝ) - 1) * (P.Vh - P.Vl) =
    (P.c - c1 P) * ((2 * (P.N : ℝ) - 1) * (2 * (P.N : ℝ) + 1) / (2 * (P.N : ℝ))) := by
  have hn0 : (P.N : ℝ) ≠ 0 := by linarith
  have hn1 : (2 * (P.N : ℝ) + 1) ≠ 0 := by linarith
  have hn2 : (2 * (P.N : ℝ) - 1) ≠ 0 := by linarith
  unfold c1
  field_simp

lemma c12 (P : Params) (hn : (1 : ℝ) < P.N) :
    c2 P - c1 P = (P.N : ℝ) * (P.Vh - P.Vl) / ((2 * (P.N : ℝ) + 1) * (2 * (P.N : ℝ) - 1)) := by
  have hn1 : (2 * (P.N : ℝ) + 1) ≠ 0 := by linarith
  have hn2 : (2 * (P.N : ℝ) - 1) ≠ 0 := by linarith
  unfold c1 c2
  rw [div_sub_div _ _ hn1 (mul_ne_zero hn1 hn2),
    div_eq_div_iff (mul_ne_zero hn1 (mul_ne_zero hn1 hn2)) (mul_ne_zero hn1 hn2)]
  ring

lemma Kid (P : Params) (hn : (1 : ℝ) < P.N) :
    P.Vh - P.Vl - 2 * (((P.N : ℝ) - 1) / (P.N : ℝ) * P.c) =
    2 * ((P.N : ℝ) - 1) / (P.N : ℝ) * (c2 P - P.c) + 3 * (P.Vh - P.Vl) / (2 * (P.N : ℝ) + 1) := by
  have hn0 : (P.N : ℝ) ≠ 0 := by linarith
  have hn1 : (2 * (P.N : ℝ) + 1) ≠ 0 := by linarith
  unfold c2
  field_simp
  ring

lemma w_eq_all (P : Params) (hn : (1 : ℝ) < P.N) (k : FeeStructure) (Vb Vs : ℝ) {φ : Fin 3 → ℝ}
    (h : PlaysAll P k Vb Vs) (hφ : MarkovChain.IsStationary (eqChain P k Vb Vs) φ) :
    welfare P φ = (P.Vh - P.Vl) / 3 - 2 * P.c * ((P.N : ℝ) - 1) / (3 * (P.N : ℝ)) := by
  unfold eqChain at hφ
  exact w_all P hn (Or.inl h) h hφ

lemma w_eq_own (P : Params) (hn : (1 : ℝ) < P.N) (k : FeeStructure) (Vb Vs : ℝ) {φ : Fin 3 → ℝ}
    (h : PlaysOwn P k Vb Vs) (hφ : MarkovChain.IsStationary (eqChain P k Vb Vs) φ) :
    welfare P φ = (P.Vh - P.Vl) / (2 * (P.N : ℝ) + 1) := by
  unfold eqChain at hφ
  exact w_own P hn (Or.inr h) h.1 hφ

lemma w_eq_none (P : Params) (k : FeeStructure) (Vb Vs : ℝ) {φ : Fin 3 → ℝ}
    (h1 : ¬ PlaysAll P k Vb Vs) (h2 : ¬ PlaysOwn P k Vb Vs)
    (hφ : MarkovChain.IsStationary (eqChain P k Vb Vs) φ) :
    welfare P φ = 0 := by
  unfold eqChain at hφ
  exact w_none P (by rintro (h | h); exact h1 h; exact h2 h) h1 hφ

lemma not_own_U (P : Params) (Vb Vs : ℝ) : ¬ PlaysOwn P .uniform Vb Vs := by
  rintro ⟨-, ⟨B, -, h1, h2⟩, -⟩
  exact h2 h1

lemma plays_all_TS (P : Params) (hn : (1 : ℝ) < P.N) (hc : 0 < P.c) (k : ℝ)
    (hk : 2 * (P.N : ℝ) * k = P.c * (2 * (P.N : ℝ) - 1)) (Vb Vs : ℝ)
    (hb : 2 * Vb = P.Vh - P.Vl - Vs - 2 * k) (ha : 2 * Vs = P.Vh - P.Vl - Vb - 2 * k) :
    PlaysAll P .tradeSpecific Vb Vs := by
  refine ⟨⟨Vs + P.Vl + P.c, ?_, ?_, ?_⟩, ⟨P.Vh - Vb - P.c, ?_, ?_, ?_⟩⟩
  · rw [bidTS]
    have e : Vs + P.Vl + P.c - P.Vl - Vs = P.c := by ring
    rw [e]
    have := hTS_ge (P.N : ℝ) P.c k (P.Vh - P.Vl - Vs) P.c hn hc hk le_rfl
    linarith
  · simp only [SellerHits, fee_ts_t]; linarith
  · simp only [SellerHits, fee_ts_f]; linarith
  · rw [askTS]
    have e : P.Vh - (P.Vh - Vb - P.c) - Vb = P.c := by ring
    rw [e]
    have := hTS_ge (P.N : ℝ) P.c k (P.Vh - P.Vl - Vb) P.c hn hc hk le_rfl
    linarith
  · simp only [BuyerHits, fee_ts_t]; linarith
  · simp only [BuyerHits, fee_ts_f]; linarith

lemma plays_own_TS (P : Params) (hn : (1 : ℝ) < P.N) (hc : 0 < P.c) (k : ℝ)
    (hk : 2 * (P.N : ℝ) * k = P.c * (2 * (P.N : ℝ) - 1)) (Vb Vs : ℝ)
    (hb : 2 * (P.N : ℝ) * Vb = P.Vh - P.Vl - Vs) (hb' : P.Vh - P.Vl - Vs - 2 * k < 2 * Vb)
    (ha : 2 * (P.N : ℝ) * Vs = P.Vh - P.Vl - Vb) (_ha' : P.Vh - P.Vl - Vb - 2 * k < 2 * Vs) :
    PlaysOwn P .tradeSpecific Vb Vs := by
  have hn0 : (2 * (P.N : ℝ)) ≠ 0 := by linarith
  refine ⟨?_, ⟨Vs + P.Vl, ?_, ?_, ?_⟩, ⟨P.Vh - Vb, ?_, ?_, ?_⟩⟩
  · rintro ⟨⟨B, hB, -, h2⟩, -⟩
    simp only [SellerHits, fee_ts_f] at h2
    rw [bidTS] at hB
    have := hTS_ge (P.N : ℝ) P.c k (P.Vh - P.Vl - Vs) (B - P.Vl - Vs) hn hc hk (by linarith)
    linarith
  · rw [bidTS]
    have e : Vs + P.Vl - P.Vl - Vs = 0 := by ring
    rw [e]
    have := hTS_zero (P.N : ℝ) P.c (P.Vh - P.Vl - Vs) hn hc
    exact mul_left_cancel₀ hn0 (by linarith)
  · simp only [SellerHits, fee_ts_t]; linarith
  · intro h; simp only [SellerHits, fee_ts_f] at h; linarith
  · rw [askTS]
    have e : P.Vh - (P.Vh - Vb) - Vb = 0 := by ring
    rw [e]
    have := hTS_zero (P.N : ℝ) P.c (P.Vh - P.Vl - Vb) hn hc
    exact mul_left_cancel₀ hn0 (by linarith)
  · simp only [BuyerHits, fee_ts_t]; linarith
  · intro h; simp only [BuyerHits, fee_ts_f] at h; linarith

lemma plays_all_U (P : Params) (hN : (0 : ℝ) < P.N) (Vb Vs : ℝ)
    (hb : 2 * Vb = P.Vh - P.Vl - 2 * (((P.N : ℝ) - 1) / (P.N : ℝ) * P.c) - Vs)
    (ha : 2 * Vs = P.Vh - P.Vl - 2 * (((P.N : ℝ) - 1) / (P.N : ℝ) * P.c) - Vb) :
    PlaysAll P .uniform Vb Vs := by
  refine ⟨⟨Vs + P.Vl + ((P.N : ℝ) - 1) / (P.N : ℝ) * P.c, ?_, ?_, ?_⟩,
    ⟨P.Vh - Vb - ((P.N : ℝ) - 1) / (P.N : ℝ) * P.c, ?_, ?_, ?_⟩⟩
  · rw [bidU P hN]
    unfold hU
    rw [if_pos (by linarith)]
    linarith
  · simp only [SellerHits, fee_u]; linarith
  · simp only [SellerHits, fee_u]; linarith
  · rw [askU P hN]
    unfold hU
    rw [if_pos (by linarith)]
    linarith
  · simp only [BuyerHits, fee_u]; linarith
  · simp only [BuyerHits, fee_u]; linarith

lemma eqTS_facts (P : Params) (hn : (1 : ℝ) < P.N) (hc : 0 < P.c) (k : ℝ)
    (hk : 2 * (P.N : ℝ) * k = P.c * (2 * (P.N : ℝ) - 1)) (Vb Vs : ℝ)
    (h : IsEquilibrium P .tradeSpecific Vb Vs) :
    ((P.Vh - P.Vl - Vs ≤ 2 * (P.N : ℝ) * Vb ∧ P.Vh - P.Vl - Vs - 2 * k ≤ 2 * Vb ∧ 0 ≤ Vb ∧
      (2 * (P.N : ℝ) * Vb = P.Vh - P.Vl - Vs ∨ 2 * Vb = P.Vh - P.Vl - Vs - 2 * k ∨ Vb = 0)) ∧
    (P.Vh - P.Vl - Vb ≤ 2 * (P.N : ℝ) * Vs ∧ P.Vh - P.Vl - Vb - 2 * k ≤ 2 * Vs ∧ 0 ≤ Vs ∧
      (2 * (P.N : ℝ) * Vs = P.Vh - P.Vl - Vb ∨ 2 * Vs = P.Vh - P.Vl - Vb - 2 * k ∨ Vs = 0))) := by
  obtain ⟨hb, ha⟩ := h
  constructor
  · apply sideTS (P.N : ℝ) P.c k (P.Vh - P.Vl - Vs) Vb hn hc hk
    · obtain ⟨B, hB⟩ := hb.1
      exact ⟨B - P.Vl - Vs, by rw [← bidTS]; exact hB⟩
    · intro u
      have := hb.2 (Set.mem_range_self (u + P.Vl + Vs))
      rw [bidTS] at this
      have e : u + P.Vl + Vs - P.Vl - Vs = u := by ring
      rwa [e] at this
  · apply sideTS (P.N : ℝ) P.c k (P.Vh - P.Vl - Vb) Vs hn hc hk
    · obtain ⟨A, hA⟩ := ha.1
      exact ⟨P.Vh - A - Vb, by rw [← askTS]; exact hA⟩
    · intro u
      have := ha.2 (Set.mem_range_self (P.Vh - u - Vb))
      rw [askTS] at this
      have e : P.Vh - (P.Vh - u - Vb) - Vb = u := by ring
      rwa [e] at this

lemma eqU_facts (P : Params) (hN : (0 : ℝ) < P.N) (Vb Vs : ℝ)
    (h : IsEquilibrium P .uniform Vb Vs) :
    ((P.Vh - P.Vl - 2 * (((P.N : ℝ) - 1) / (P.N : ℝ) * P.c) - Vs ≤ 2 * Vb ∧ 0 ≤ Vb ∧
      (2 * Vb = P.Vh - P.Vl - 2 * (((P.N : ℝ) - 1) / (P.N : ℝ) * P.c) - Vs ∨ Vb = 0)) ∧
    (P.Vh - P.Vl - 2 * (((P.N : ℝ) - 1) / (P.N : ℝ) * P.c) - Vb ≤ 2 * Vs ∧ 0 ≤ Vs ∧
      (2 * Vs = P.Vh - P.Vl - 2 * (((P.N : ℝ) - 1) / (P.N : ℝ) * P.c) - Vb ∨ Vs = 0))) := by
  obtain ⟨hb, ha⟩ := h
  constructor
  · apply sideU
    · obtain ⟨B, hB⟩ := hb.1
      exact ⟨_, by rw [← bidU P hN]; exact hB⟩
    · intro u
      have := hb.2 (Set.mem_range_self (u + P.Vl + ((P.N : ℝ) - 1) / (P.N : ℝ) * P.c + Vs))
      rw [bidU P hN] at this
      have e : u + P.Vl + ((P.N : ℝ) - 1) / (P.N : ℝ) * P.c + Vs - P.Vl -
          ((P.N : ℝ) - 1) / (P.N : ℝ) * P.c - Vs = u := by ring
      rwa [e] at this
  · apply sideU
    · obtain ⟨A, hA⟩ := ha.1
      exact ⟨_, by rw [← askU P hN]; exact hA⟩
    · intro u
      have := ha.2 (Set.mem_range_self (P.Vh - u - ((P.N : ℝ) - 1) / (P.N : ℝ) * P.c - Vb))
      rw [askU P hN] at this
      have e : P.Vh - (P.Vh - u - ((P.N : ℝ) - 1) / (P.N : ℝ) * P.c - Vb) -
          ((P.N : ℝ) - 1) / (P.N : ℝ) * P.c - Vb = u := by ring
      rwa [e] at this

end PTF5d

open PostTradeFees.Welfare in
theorem solution (P : Params) (hS : P.Standing)
    (φa φo : Fin 3 → ℝ)
    (hφa : MarkovChain.IsStationary (chainAll P.N) φa)
    (hφo : MarkovChain.IsStationary (chainOwn P.N) φo)
    (VbU VsU VbT VsT : ℝ)
    (hU : IsEquilibrium P .uniform VbU VsU)
    (hT : IsEquilibrium P .tradeSpecific VbT VsT)
    (φU φT : Fin 3 → ℝ)
    (hφU : MarkovChain.IsStationary (eqChain P .uniform VbU VsU) φU)
    (hφT : MarkovChain.IsStationary (eqChain P .tradeSpecific VbT VsT) φT) :
    (P.c ≤ c1 P →
      welfare P φo < welfare P φa ∧
      PlaysAll P .uniform VbU VsU ∧ PlaysAll P .tradeSpecific VbT VsT ∧
      welfare P φU = welfare P φa ∧ welfare P φT = welfare P φa) ∧
    (c1 P < P.c → P.c ≤ c2 P →
      welfare P φo ≤ welfare P φa ∧
      PlaysAll P .uniform VbU VsU ∧ PlaysOwn P .tradeSpecific VbT VsT ∧
      welfare P φU = welfare P φa ∧ welfare P φT = welfare P φo) ∧
    (c2 P < P.c →
      welfare P φa < welfare P φo ∧
      PlaysOwn P .tradeSpecific VbT VsT ∧ ¬ PlaysOwn P .uniform VbU VsU ∧
      welfare P φT = welfare P φo ∧ welfare P φU < welfare P φT) := by
  obtain ⟨hN1, hVl, hVlh, hc⟩ := hS
  have hn : (1 : ℝ) < P.N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < P.N := by linarith
  have hD : 0 < P.Vh - P.Vl := by linarith
  have hk : 2 * (P.N : ℝ) * (P.c * (2 * (P.N : ℝ) - 1) / (2 * (P.N : ℝ))) =
      P.c * (2 * (P.N : ℝ) - 1) := by field_simp
  have hk0 : 0 < P.c * (2 * (P.N : ℝ) - 1) / (2 * (P.N : ℝ)) :=
    div_pos (mul_pos hc (by linarith)) (by linarith)
  obtain ⟨⟨B1, B2, B3, B4⟩, ⟨A1, A2, A3, A4⟩⟩ := PTF5d.eqTS_facts P hn hc _ hk VbT VsT hT
  have core := PTF5d.coreTS (P.N : ℝ) (P.Vh - P.Vl) _ VbT VsT hn hD hk0 B1 B2 B3 B4 A1 A2 A3 A4
  obtain ⟨⟨U1, U3, U4⟩, ⟨V1, V3, V4⟩⟩ := PTF5d.eqU_facts P hN0 VbU VsU hU
  have wa : welfare P φa = (P.Vh - P.Vl) / 3 - 2 * P.c * ((P.N : ℝ) - 1) / (3 * (P.N : ℝ)) :=
    PTF5d.w_all P hn trivial trivial hφa
  have wo : welfare P φo = (P.Vh - P.Vl) / (2 * (P.N : ℝ) + 1) :=
    PTF5d.w_own P hn trivial (fun h => h) hφo
  have hreg := PTF5d.reg_id P hn
  have hc12 := PTF5d.c12 P hn
  have hwd := PTF5d.wdiff P hn
  have hK := PTF5d.Kid P hn
  have F1 : 0 < (2 * (P.N : ℝ) - 1) * (2 * (P.N : ℝ) + 1) / (2 * (P.N : ℝ)) :=
    div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have F2 : 0 < 2 * ((P.N : ℝ) - 1) / (3 * (P.N : ℝ)) :=
    div_pos (by linarith) (by linarith)
  have F3 : 0 < 2 * ((P.N : ℝ) - 1) / (P.N : ℝ) := div_pos (by linarith) hN0
  have hc12p : 0 < c2 P - c1 P := by
    rw [hc12]; exact div_pos (mul_pos hN0 hD) (mul_pos (by linarith) (by linarith))
  have hO : 0 < (P.Vh - P.Vl) / (2 * (P.N : ℝ) + 1) := div_pos hD (by linarith)
  have hO3 : 0 < 3 * (P.Vh - P.Vl) / (2 * (P.N : ℝ) + 1) := div_pos (by linarith) (by linarith)
  have uniAll : P.c ≤ c2 P → PlaysAll P .uniform VbU VsU := by
    intro h
    have hKpos : 0 < P.Vh - P.Vl - 2 * (((P.N : ℝ) - 1) / (P.N : ℝ) * P.c) := by
      rw [hK]
      have := mul_nonneg F3.le (sub_nonneg.mpr h)
      linarith
    obtain ⟨u1, u2⟩ := PTF5d.coreU _ VbU VsU hKpos U1 U3 U4 V1 V3 V4
    exact PTF5d.plays_all_U P hN0 VbU VsU u1 u2
  have tsOwn : c1 P < P.c → PlaysOwn P .tradeSpecific VbT VsT := by
    intro h
    have : 0 < (P.c - c1 P) * ((2 * (P.N : ℝ) - 1) * (2 * (P.N : ℝ) + 1) / (2 * (P.N : ℝ))) :=
      mul_pos (by linarith) F1
    obtain ⟨o1, o2, o3, o4⟩ := core.2 (by linarith)
    exact PTF5d.plays_own_TS P hn hc _ hk VbT VsT o1 o2 o3 o4
  refine ⟨fun h1 => ?_, fun h1 h2 => ?_, fun h3 => ?_⟩
  · have : (P.c - c1 P) * ((2 * (P.N : ℝ) - 1) * (2 * (P.N : ℝ) + 1) / (2 * (P.N : ℝ))) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) F1.le
    obtain ⟨e1, e2⟩ := core.1 (by linarith)
    have hTall := PTF5d.plays_all_TS P hn hc _ hk VbT VsT e1 e2
    have hUall := uniAll (by linarith)
    refine ⟨?_, hUall, hTall, ?_, ?_⟩
    · rw [wa, wo]
      have := mul_pos F2 (show 0 < c2 P - P.c by linarith)
      linarith
    · rw [PTF5d.w_eq_all P hn _ _ _ hUall hφU, wa]
    · rw [PTF5d.w_eq_all P hn _ _ _ hTall hφT, wa]
  · have hTown := tsOwn h1
    have hUall := uniAll h2
    refine ⟨?_, hUall, hTown, ?_, ?_⟩
    · rw [wa, wo]
      have := mul_nonneg F2.le (show 0 ≤ c2 P - P.c by linarith)
      linarith
    · rw [PTF5d.w_eq_all P hn _ _ _ hUall hφU, wa]
    · rw [PTF5d.w_eq_own P hn _ _ _ hTown hφT, wo]
  · have hTown := tsOwn (by linarith)
    have hneg := mul_neg_of_pos_of_neg F2 (show c2 P - P.c < 0 by linarith)
    refine ⟨?_, hTown, PTF5d.not_own_U P VbU VsU, ?_, ?_⟩
    · rw [wa, wo]; linarith
    · rw [PTF5d.w_eq_own P hn _ _ _ hTown hφT, wo]
    · rw [PTF5d.w_eq_own P hn _ _ _ hTown hφT]
      by_cases hUa : PlaysAll P .uniform VbU VsU
      · rw [PTF5d.w_eq_all P hn _ _ _ hUa hφU]; linarith
      · rw [PTF5d.w_eq_none P _ _ _ hUa (PTF5d.not_own_U P VbU VsU) hφU]; exact hO

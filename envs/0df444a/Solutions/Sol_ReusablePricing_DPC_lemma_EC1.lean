-- Prove2me | solution 1 for ReusablePricing.DPC.lemma_EC1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T03:58:02.637469+00:00
-- url     : https://prove2.me/submissions/f1d84d3d-43ba-4c66-a003-c14aeb3c8cb0

import Mathlib
import Definitions.Def_ReusablePricing_DPC_Model
import Definitions.Def_ReusablePricing_DPC_Control

open Finset ReusablePricing.DPC

/-- Prefix sum `F(x) = ∑_{s=1}^{x} Δ^s_j`. -/
noncomputable def dpcF (P : Basic) (ε : ℝ) (nl : ℕ) (ω : P.Path) (j : Fin P.J) (x : ℕ) : ℝ :=
  ∑ s ∈ Ioc 0 x, P.Delta ε nl s ω j

lemma dpcF_sub (P : Basic) (ε : ℝ) (nl : ℕ) (ω : P.Path) (j : Fin P.J) (a c : ℕ) (h : a ≤ c) :
    dpcF P ε nl ω j c - dpcF P ε nl ω j a = ∑ s ∈ Ioc a c, P.Delta ε nl s ω j := by
  unfold dpcF
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) h]
  ring

/-- On `𝒢`, prefix sums move by less than `δ` inside a service cycle. -/
lemma dpc_block (P : Basic) (ε : ℝ) (nl : ℕ) (δ : ℝ) (ω : P.Path) (hG : P.InG ε nl δ ω)
    (hδ : 0 < δ) (j : Fin P.J) (b : ℕ) (hb : b ∈ Icc 1 (P.T / P.n)) (x : ℕ)
    (hx1 : (b - 1) * P.n ≤ x) (hx2 : x ≤ b * P.n) :
    |dpcF P ε nl ω j x - dpcF P ε nl ω j ((b - 1) * P.n)| < δ := by
  rcases hx1.lt_or_eq with hlt | heq
  · rw [dpcF_sub P ε nl ω j _ _ hx1, ← Finset.Icc_add_one_left_eq_Ioc]
    exact hG j b hb x (Finset.mem_Icc.mpr ⟨hlt, hx2⟩)
  · rw [heq, sub_self, abs_zero]; exact hδ

/-- On `𝒢`, every window of length at most `n` inside `[1, T]` carries `|∑ Δ| < 3δ`. -/
lemma dpc_window (P : Basic) (ε : ℝ) (nl : ℕ) (δ : ℝ) (ω : P.Path) (hG : P.InG ε nl δ ω)
    (hδ : 0 < δ) (hn : 1 ≤ P.n) (hdvd : P.n ∣ P.T) (j : Fin P.J) (a c : ℕ)
    (hac : a ≤ c) (hcT : c ≤ P.T) (hcn : c ≤ a + P.n) :
    |∑ s ∈ Ioc a c, P.Delta ε nl s ω j| < 3 * δ := by
  rw [← dpcF_sub P ε nl ω j a c hac]
  rcases hac.lt_or_eq with hlt | heq
  swap
  · rw [heq, sub_self, abs_zero]; linarith
  obtain ⟨q, hq1, hq2⟩ : ∃ q, q * P.n ≤ a ∧ a < (q + 1) * P.n := by
    refine ⟨a / P.n, Nat.div_mul_le_self a P.n, ?_⟩
    have := Nat.lt_div_mul_add (a := a) (b := P.n) (by omega)
    rw [add_mul, one_mul]; exact this
  obtain ⟨k, hk⟩ := hdvd
  have hTn : P.T / P.n = k := by rw [hk, Nat.mul_div_cancel_left _ (by omega)]
  have hqk : q * P.n < k * P.n := by nlinarith
  have hqk' : q < k := lt_of_mul_lt_mul_right hqk (Nat.zero_le _)
  have hb1 : q + 1 ∈ Icc 1 (P.T / P.n) := by rw [hTn, Finset.mem_Icc]; omega
  have hA := dpc_block P ε nl δ ω hG hδ j (q + 1) hb1 a (by simpa using hq1) hq2.le
  simp only [Nat.add_sub_cancel] at hA
  by_cases hc : c ≤ (q + 1) * P.n
  · have hC := dpc_block P ε nl δ ω hG hδ j (q + 1) hb1 c
      (by simp only [Nat.add_sub_cancel]; omega) hc
    simp only [Nat.add_sub_cancel] at hC
    have : |dpcF P ε nl ω j c - dpcF P ε nl ω j a| ≤
        |dpcF P ε nl ω j c - dpcF P ε nl ω j (q * P.n)| +
          |dpcF P ε nl ω j a - dpcF P ε nl ω j (q * P.n)| := by
      rw [show dpcF P ε nl ω j c - dpcF P ε nl ω j a =
        (dpcF P ε nl ω j c - dpcF P ε nl ω j (q * P.n)) -
          (dpcF P ε nl ω j a - dpcF P ε nl ω j (q * P.n)) by ring]
      exact abs_sub _ _
    linarith
  · push Not at hc
    have hc2 : c ≤ (q + 2) * P.n := by
      have : a + P.n < (q + 2) * P.n := by rw [show q + 2 = (q + 1) + 1 by ring, add_mul]; omega
      omega
    have hqk2 : (q + 1) * P.n < k * P.n := by nlinarith
    have hqk2' : q + 1 < k := lt_of_mul_lt_mul_right hqk2 (Nat.zero_le _)
    have hb2 : q + 2 ∈ Icc 1 (P.T / P.n) := by rw [hTn, Finset.mem_Icc]; omega
    have hC := dpc_block P ε nl δ ω hG hδ j (q + 2) hb2 c
      (by rw [show q + 2 - 1 = q + 1 by omega]; omega) hc2
    rw [show q + 2 - 1 = q + 1 by omega] at hC
    have hB := dpc_block P ε nl δ ω hG hδ j (q + 1) hb1 ((q + 1) * P.n)
      (by simp only [Nat.add_sub_cancel]; exact Nat.mul_le_mul_right _ (Nat.le_succ q)) le_rfl
    simp only [Nat.add_sub_cancel] at hB
    have : |dpcF P ε nl ω j c - dpcF P ε nl ω j a| ≤
        |dpcF P ε nl ω j c - dpcF P ε nl ω j ((q + 1) * P.n)| +
        |dpcF P ε nl ω j ((q + 1) * P.n) - dpcF P ε nl ω j (q * P.n)| +
          |dpcF P ε nl ω j a - dpcF P ε nl ω j (q * P.n)| := by
      have e : dpcF P ε nl ω j c - dpcF P ε nl ω j a =
        (dpcF P ε nl ω j c - dpcF P ε nl ω j ((q + 1) * P.n)) +
        (dpcF P ε nl ω j ((q + 1) * P.n) - dpcF P ε nl ω j (q * P.n)) -
          (dpcF P ε nl ω j a - dpcF P ε nl ω j (q * P.n)) := by ring
      rw [e]
      exact (abs_sub _ _).trans (by gcongr; exact abs_add_le _ _)
    linarith

/-- `δ > 0` whenever `𝒢(ε, δ)` is nonempty. -/
lemma dpc_delta_pos (P : Basic) (ε : ℝ) (nl : ℕ) (δ : ℝ) (ω : P.Path) (hG : P.InG ε nl δ ω)
    (hJ : 1 ≤ P.J) (hn : 1 ≤ P.n) (hT : 1 ≤ P.T) (hdvd : P.n ∣ P.T) : 0 < δ := by
  have hb : 1 ∈ Icc 1 (P.T / P.n) := by
    rw [Finset.mem_Icc]; exact ⟨le_rfl, (Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega) hdvd)⟩
  have h := hG ⟨0, by omega⟩ 1 hb 1 (by rw [Finset.mem_Icc]; simp; omega)
  exact lt_of_le_of_lt (abs_nonneg _) h

/-- DPC never posts more than the shifted DET rate (given (ii)). -/
lemma dpc_rate_le (P : Basic) (ε : ℝ) (nl : ℕ) (s : ℕ) (ω : P.Path) (j : Fin P.J)
    (h0 : 0 ≤ P.lamD s j) (hU : 0 ≤ P.lamU)
    (hii : 0 < P.lamD s j → 0 < P.lamD s j - ε / nl ∧ P.lamD s j - ε / nl < P.lamU) :
    P.dpcRate ε nl s ω j ≤ P.lamD s j - ε / nl * (if 0 < P.lamD s j then 1 else 0) := by
  unfold Basic.dpcRate
  by_cases hpos : 0 < P.lamD s j
  · obtain ⟨ha, hb⟩ := hii hpos
    rw [if_pos hpos, mul_one]
    split_ifs
    · rw [min_eq_right hb.le, max_eq_right ha.le]
    · exact ha.le
  · have : P.lamD s j = 0 := le_antisymm (not_lt.mp hpos) h0
    rw [if_neg hpos, mul_zero, sub_zero, this]
    split_ifs
    · simp [hU]
    · exact le_rfl

/-- On a path of positive probability, a type with zero DET rate in period `s` has no arrival. -/
lemma dpc_D_zero (P : Basic) (ε : ℝ) (nl : ℕ) (s : ℕ) (ω : P.Path) (j : Fin P.J)
    (hω : 0 < P.pathProb ε nl ω) (hU : 0 ≤ P.lamU) (hz : P.lamD s j = 0) :
    P.D s ω j = 0 := by
  unfold Basic.D
  rw [if_neg]
  intro hout
  have hs : s ∈ Icc 1 P.T := by
    unfold Basic.outcome at hout
    split_ifs at hout with h
    · exact Finset.mem_Icc.mpr h
  have hr : P.dpcRate ε nl s ω j = 0 := by
    unfold Basic.dpcRate
    rw [hz]
    split_ifs with h1 h2
    · exact absurd h2 (lt_irrefl 0)
    · simp [hU]
    · rfl
  have : P.pathProb ε nl ω = 0 := by
    unfold Basic.pathProb
    apply Finset.prod_eq_zero hs
    rw [hout]
    simp [Basic.q, hr]
  linarith

/-- Per-type capacity estimate on one window. -/
lemma dpc_type_bound (P : Basic) (ε : ℝ) (nl : ℕ) (δ : ℝ) (ω : P.Path) (j : Fin P.J)
    (W K : Finset ℕ) (hWK : W ⊆ K) (hK : K ⊆ Icc 1 P.T)
    (hω : 0 < P.pathProb ε nl ω) (hU : 0 ≤ P.lamU)
    (h0 : ∀ s ∈ Icc 1 P.T, 0 ≤ P.lamD s j)
    (hii : ∀ s ∈ Icc 1 P.T, 0 < P.lamD s j →
      0 < P.lamD s j - ε / nl ∧ P.lamD s j - ε / nl < P.lamU)
    (hwin : |∑ s ∈ W, P.Delta ε nl s ω j| < 3 * δ) (h3 : 3 * δ < ε) (hnl : (0 : ℝ) < nl)
    (hcnt : 0 < (K.filter (fun s => 0 < P.lamD s j)).card →
      nl ≤ (K.filter (fun s => 0 < P.lamD s j)).card) :
    (∑ s ∈ W, P.D s ω j = 0 ∨ ∑ s ∈ W, P.D s ω j < ∑ s ∈ K, P.lamD s j) ∧
      ∑ s ∈ W, P.D s ω j ≤ ∑ s ∈ K, P.lamD s j := by
  have hΛ0 : 0 ≤ ∑ s ∈ K, P.lamD s j := Finset.sum_nonneg (fun s hs => h0 s (hK hs))
  by_cases hc : (K.filter (fun s => 0 < P.lamD s j)).card = 0
  · have hz : ∀ s ∈ K, P.lamD s j = 0 := by
      intro s hs
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hc
      exact le_antisymm (not_lt.mp (hc hs)) (h0 s (hK hs))
    have hD : ∑ s ∈ W, P.D s ω j = 0 :=
      Finset.sum_eq_zero (fun s hs => dpc_D_zero P ε nl s ω j hω hU (hz s (hWK hs)))
    rw [hD]; exact ⟨Or.inl rfl, hΛ0⟩
  · have hge := hcnt (Nat.pos_of_ne_zero hc)
    set c := ε / nl with hcdef
    have hsplit : ∑ s ∈ W, P.D s ω j =
        ∑ s ∈ W, P.dpcRate ε nl s ω j + ∑ s ∈ W, P.Delta ε nl s ω j := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro s _
      unfold Basic.Delta; ring
    have hr1 : ∑ s ∈ W, P.dpcRate ε nl s ω j ≤
        ∑ s ∈ W, (P.lamD s j - c * (if 0 < P.lamD s j then 1 else 0)) :=
      Finset.sum_le_sum (fun s hs => dpc_rate_le P ε nl s ω j (h0 s (hK (hWK hs))) hU
        (hii s (hK (hWK hs))))
    have hr2 : ∑ s ∈ W, (P.lamD s j - c * (if 0 < P.lamD s j then 1 else 0)) ≤
        ∑ s ∈ K, (P.lamD s j - c * (if 0 < P.lamD s j then 1 else 0)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hWK
      intro s hs _
      by_cases hp : 0 < P.lamD s j
      · rw [if_pos hp, mul_one]; exact (hii s (hK hs) hp).1.le
      · rw [if_neg hp, mul_zero, sub_zero]; exact h0 s (hK hs)
    have hr3 : ∑ s ∈ K, (P.lamD s j - c * (if 0 < P.lamD s j then 1 else 0)) =
        ∑ s ∈ K, P.lamD s j - c * ((K.filter (fun s => 0 < P.lamD s j)).card : ℝ) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
    have hr4 : ε ≤ c * ((K.filter (fun s => 0 < P.lamD s j)).card : ℝ) := by
      have : (nl : ℝ) ≤ (K.filter (fun s => 0 < P.lamD s j)).card := by exact_mod_cast hge
      have hc0 : 0 ≤ c := by rw [hcdef]; exact div_nonneg (by linarith [h3, abs_nonneg (∑ s ∈ W, P.Delta ε nl s ω j)]) hnl.le
      calc ε = c * nl := by rw [hcdef]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left this hc0
    have hlt : ∑ s ∈ W, P.D s ω j < ∑ s ∈ K, P.lamD s j := by
      have := lt_of_le_of_lt (le_abs_self _) hwin
      linarith
    exact ⟨Or.inr hlt, hlt.le⟩

lemma dpc_sum_nat (P : Basic) (W : Finset ℕ) (ω : P.Path) (i : Fin P.I) :
    ∃ N : ℕ, ∑ s ∈ W, ∑ j, (P.A i j : ℝ) * P.D s ω j = (N : ℝ) := by
  refine ⟨∑ s ∈ W, ∑ j, P.A i j * (if P.outcome s ω = some j then 1 else 0), ?_⟩
  push_cast
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro j _
  unfold Basic.D
  split_ifs <;> simp

theorem solution (P : Basic) (φL φU Ψ R : ℝ) (nl : ℕ) (ε δ : ℝ)
    (hP : P.Standing φL φU Ψ R nl)
    (hε : ε ≤ min φL φU * nl)
    (hδ : δ = ((nl : ℝ) - 1) * (ε - 1) / (3 * nl))
    (ω : P.Path) (hω : 0 < P.pathProb ε nl ω) (hG : P.InG ε nl δ ω) :
    ∀ t ∈ Icc 1 P.T,
      (∀ i, 1 ≤ P.freeCap t ω i) ∧
      ∀ j, 0 < P.lamD t j →
        0 < P.lamD t j - ε / nl ∧ P.lamD t j - ε / nl < P.lamU := by
  obtain ⟨hMF, hOpt, hWL, -, hA5, hNb, -⟩ := hP
  obtain ⟨-, hJ1, hn1, hT1, hdvd, hA1, -, hC1, hU0, -, -⟩ := hMF
  obtain ⟨hφL, hφU, -, hA5t⟩ := hA5
  have hnT : P.n ≤ P.T := Nat.le_of_dvd (by omega) hdvd
  have hδpos := dpc_delta_pos P ε nl δ ω hG hJ1 hn1 hT1 hdvd
  have hnlN : 0 < nl := by
    obtain ⟨-, j, t, -, hc, he⟩ := hNb
    omega
  have hnl : (0 : ℝ) < nl := by exact_mod_cast hnlN
  have hnl1 : (1 : ℝ) ≤ nl := by exact_mod_cast hnlN
  have hε1 : 1 < ε := by
    by_contra hc
    push Not at hc
    have : ((nl : ℝ) - 1) * (ε - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have : δ ≤ 0 := by rw [hδ]; exact div_nonpos_of_nonpos_of_nonneg this (by positivity)
    linarith
  have h3 : 3 * δ < ε := by
    have e : 3 * δ * nl = ((nl : ℝ) - 1) * (ε - 1) := by rw [hδ]; field_simp
    by_contra hc
    push Not at hc
    have := mul_le_mul_of_nonneg_right hc hnl.le
    nlinarith
  have hc_le : ε / nl ≤ φL := by
    rw [div_le_iff₀ hnl]; exact le_trans hε (mul_le_mul_of_nonneg_right (min_le_left _ _) hnl.le)
  have hc_pos : 0 < ε / nl := div_pos (by linarith) hnl
  have h0 : ∀ j, ∀ s ∈ Icc 1 P.T, 0 ≤ P.lamD s j := fun j s hs => (hOpt.1.1 s hs j).1
  have hii : ∀ j, ∀ s ∈ Icc 1 P.T, 0 < P.lamD s j →
      0 < P.lamD s j - ε / nl ∧ P.lamD s j - ε / nl < P.lamU := by
    intro j s hs hpos
    rcases hWL s hs j with hz | ⟨hp, hlt⟩
    · linarith
    · obtain ⟨h1, h2⟩ := (hA5t s hs).1 j hp hlt
      constructor <;> linarith
  intro t ht
  refine ⟨?_, fun j hpos => hii j t ht hpos⟩
  intro i
  rw [Finset.mem_Icc] at ht
  set u := P.winStart t with hu
  have hu1 : 1 ≤ u := le_max_left _ _
  have hu2 : t + 1 - P.n ≤ u := le_max_right _ _
  have hut : u ≤ t := max_le ht.1 (by omega)
  have huT : u + P.n - 1 ≤ P.T := by
    rcases le_total t P.n with h | h
    · have : u = 1 := le_antisymm (max_le le_rfl (by omega)) hu1
      omega
    · have : u = t + 1 - P.n := le_antisymm (max_le (by omega) le_rfl) hu2
      omega
  set K := Icc u (u + P.n - 1) with hK
  set W := Icc u (t - 1) with hWdef
  have hWK : W ⊆ K := Finset.Icc_subset_Icc le_rfl (by omega)
  have hKT : K ⊆ Icc 1 P.T := Finset.Icc_subset_Icc hu1 huT
  have hwin : ∀ j, |∑ s ∈ W, P.Delta ε nl s ω j| < 3 * δ := by
    intro j
    have hWI : W = Ioc (u - 1) (t - 1) := by
      rw [hWdef, ← Finset.Icc_add_one_left_eq_Ioc, Nat.sub_add_cancel hu1]
    rw [hWI]
    exact dpc_window P ε nl δ ω hG hδpos hn1 hdvd j (u - 1) (t - 1) (by omega) (by omega)
      (by omega)
  have hbd : ∀ j, (∑ s ∈ W, P.D s ω j = 0 ∨ ∑ s ∈ W, P.D s ω j < ∑ s ∈ K, P.lamD s j) ∧
      ∑ s ∈ W, P.D s ω j ≤ ∑ s ∈ K, P.lamD s j := by
    intro j
    refine dpc_type_bound P ε nl δ ω j W K hWK hKT hω hU0.le (h0 j) (hii j) (hwin j) h3 hnl ?_
    intro hpos
    exact hNb.1 j u (Finset.mem_Icc.mpr ⟨hu1, by omega⟩) hpos
  -- DET feasibility at period `u + n - 1`
  have hDET : ∑ j, (P.A i j : ℝ) * ∑ s ∈ K, P.lamD s j ≤ (P.C i : ℝ) := by
    have hws : P.winStart (u + P.n - 1) = u := by
      unfold Basic.winStart
      rw [show u + P.n - 1 + 1 - P.n = u by omega]; exact max_eq_right hu1
    have := hOpt.1.2 (u + P.n - 1) (Finset.mem_Icc.mpr ⟨by omega, huT⟩) i
    rw [hws, Finset.sum_comm] at this
    simpa [Finset.mul_sum] using this
  have hS : ∑ s ∈ W, ∑ j, (P.A i j : ℝ) * P.D s ω j = ∑ j, (P.A i j : ℝ) * ∑ s ∈ W, P.D s ω j := by
    rw [Finset.sum_comm]; simp [Finset.mul_sum]
  have hterm : ∀ j, (P.A i j : ℝ) * ∑ s ∈ W, P.D s ω j ≤ (P.A i j : ℝ) * ∑ s ∈ K, P.lamD s j :=
    fun j => mul_le_mul_of_nonneg_left (hbd j).2 (by positivity)
  obtain ⟨N, hN⟩ := dpc_sum_nat P W ω i
  unfold Basic.freeCap
  rw [← hu]
  change 1 ≤ (P.C i : ℝ) - ∑ s ∈ W, ∑ j, (P.A i j : ℝ) * P.D s ω j
  by_cases hall : ∀ j, (P.A i j : ℝ) * ∑ s ∈ W, P.D s ω j = 0
  · rw [hS, Finset.sum_eq_zero (fun j _ => hall j)]
    have := hC1 i
    have : (1 : ℝ) ≤ P.C i := by exact_mod_cast this
    linarith
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    have hAj : P.A i j = 1 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hA1 i j) with h | h
      · rw [h] at hj; simp at hj
      · exact h
    have hstrict : (P.A i j : ℝ) * ∑ s ∈ W, P.D s ω j < (P.A i j : ℝ) * ∑ s ∈ K, P.lamD s j := by
      rw [hAj, Nat.cast_one, one_mul, one_mul]
      rcases (hbd j).1 with h | h
      · rw [hAj, Nat.cast_one, one_mul] at hj; exact absurd h hj
      · exact h
    have hlt : ∑ s ∈ W, ∑ j, (P.A i j : ℝ) * P.D s ω j < (P.C i : ℝ) := by
      rw [hS]
      exact lt_of_lt_of_le (Finset.sum_lt_sum (fun j _ => hterm j) ⟨j, Finset.mem_univ _, hstrict⟩)
        hDET
    rw [hN] at hlt ⊢
    have : N < P.C i := by exact_mod_cast hlt
    have : N + 1 ≤ P.C i := this
    have : ((N : ℝ) + 1) ≤ P.C i := by exact_mod_cast this
    linarith

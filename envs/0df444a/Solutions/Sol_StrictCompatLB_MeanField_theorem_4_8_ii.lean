-- Prove2me | solution 1 for StrictCompatLB.MeanField.theorem_4_8_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T15:11:07.396337+00:00
-- url     : https://prove2.me/submissions/2ae8c7e1-7edb-4680-a469-0f2837b00a46

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model
import Theorems.Thm_StrictCompatLB_MeanField_theorem_4_8_i
import Theorems.Thm_StrictCompatLB_MeanField_lemma_4_9
import Theorems.Thm_StrictCompatLB_MeanField_lemma_4_10

open Filter Topology MeasureTheory Finset
open scoped ENNReal

namespace StrictCompatLB.MeanField.T48ii

open StrictCompatLB.MeanField

lemma occ_nonneg {N : ℕ} (z : Fin N → ℕ) (i : ℕ) : 0 ≤ occ z i :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma occ_le_one {N : ℕ} (z : Fin N → ℕ) (i : ℕ) : occ z i ≤ 1 := by
  unfold occ
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · rw [div_le_one (by exact_mod_cast h)]
    have : Qcount z i ≤ N := by
      unfold Qcount
      calc _ ≤ (univ : Finset (Fin N)).card := Finset.card_filter_le _ _
        _ = N := by simp
    exact_mod_cast this

lemma occ_zero_of {N : ℕ} (z : Fin N → ℕ) (i : ℕ) (hi : maxLen z < i) : occ z i = 0 := by
  have : Qcount z i = 0 := by
    unfold Qcount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro u _ hu
    have : z u ≤ maxLen z := Finset.le_sup (f := z) (mem_univ u)
    omega
  simp [occ, this]

lemma expect_le_one {N : ℕ} (π : (Fin N → ℕ) → ℝ) (hπ : IsProbVec π) (i : ℕ) :
    expectENN π (fun z => occ z i) ≤ 1 := by
  unfold expectENN
  calc _ ≤ ∑' z, ENNReal.ofReal (π z) := ENNReal.tsum_le_tsum (fun z => by
        calc _ ≤ ENNReal.ofReal (π z) * 1 :=
              mul_le_mul_right (ENNReal.ofReal_le_one.mpr (occ_le_one z i)) _
          _ = _ := mul_one _)
    _ = ENNReal.ofReal (∑' z, π z) := (ENNReal.ofReal_tsum_of_nonneg hπ.1 hπ.2.summable).symm
    _ = 1 := by rw [hπ.2.tsum_eq, ENNReal.ofReal_one]

/-- Geometric decay of the stationary occupancies from the tail-moment bound (4.18). -/
lemma geometric_decay {N : ℕ} (π : (Fin N → ℕ) → ℝ) (hπ : IsProbVec π) (a ρ : ℝ) (ha : 0 ≤ a)
    (hρ : ρ = a / (1 + a))
    (h49 : ∀ k : ℕ, 1 ≤ k →
      (∑' i : ℕ, if k ≤ i then expectENN π (fun z => occ z i) else 0) ≤
        ENNReal.ofReal a * expectENN π (fun z => occ z (k - 1))) :
    ∀ k : ℕ, 1 ≤ k → expectENN π (fun z => occ z k) ≤ ENNReal.ofReal (a * ρ ^ (k - 1)) := by
  set E : ℕ → ℝ≥0∞ := fun i => expectENN π (fun z => occ z i) with hE
  set s : ℕ → ℝ≥0∞ := fun k => ∑' i : ℕ, if k ≤ i then E i else 0 with hs
  have hE1 : ∀ i, E i ≤ 1 := fun i => expect_le_one π hπ i
  have hsplit : ∀ k, s k = E k + s (k + 1) := by
    intro k
    simp only [hs]
    · have : ∀ i, (if k ≤ i then E i else 0) = (if i = k then E i else 0) +
          (if k + 1 ≤ i then E i else 0) := by
        intro i
        by_cases h1 : i = k
        · subst h1; simp
        · by_cases h2 : k ≤ i
          · rw [if_pos h2, if_neg h1, if_pos (by omega), zero_add]
          · rw [if_neg h2, if_neg h1, if_neg (by omega), zero_add]
      simp only [this]
      rw [ENNReal.tsum_add, tsum_ite_eq]
  have hsfin : ∀ k, 1 ≤ k → s k ≤ ENNReal.ofReal a := by
    intro k hk
    calc s k ≤ ENNReal.ofReal a * E (k - 1) := h49 k hk
      _ ≤ ENNReal.ofReal a * 1 := mul_le_mul_right (hE1 _) _
      _ = _ := mul_one _
  have hsne : ∀ k, 1 ≤ k → s k ≠ ⊤ := fun k hk =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsfin k hk)
  -- the recursion `(1 + a) s_{k+1} ≤ a s_k`
  have hrec : ∀ k, 1 ≤ k → (s (k + 1)).toReal ≤ ρ * (s k).toReal := by
    intro k hk
    have h1 : s (k + 1) ≤ ENNReal.ofReal a * E k := by
      have := h49 (k + 1) (by omega)
      rw [Nat.add_sub_cancel] at this
      exact this
    have h2 : (s (k + 1)).toReal ≤ a * (E k).toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_le_ne_top ENNReal.one_ne_top (hE1 k))) h1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha] at this
    have h3 : (s k).toReal = (E k).toReal + (s (k + 1)).toReal := by
      rw [hsplit k, ENNReal.toReal_add (ne_top_of_le_ne_top ENNReal.one_ne_top (hE1 k))
        (hsne (k + 1) (by omega))]
    rw [hρ, h3]
    have : 0 < 1 + a := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ this]
    nlinarith
  have hs1 : (s 1).toReal ≤ a := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hsfin 1 le_rfl)
    rwa [ENNReal.toReal_ofReal ha] at this
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hsk : ∀ k, 1 ≤ k → (s k).toReal ≤ a * ρ ^ (k - 1) := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0; simpa using hs1
      · have := ih hpos
        calc (s (k + 1)).toReal ≤ ρ * (s k).toReal := hrec k hpos
          _ ≤ ρ * (a * ρ ^ (k - 1)) := mul_le_mul_of_nonneg_left this hρ0
          _ = a * ρ ^ (k + 1 - 1) := by
              obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
              rw [show j + 1 - 1 = j by omega, show j + 1 + 1 - 1 = j + 1 by omega, pow_succ]
              ring
  intro k hk
  calc E k ≤ s k := by
        simp only [hs]
        calc E k = (if k ≤ k then E k else 0) := by simp
          _ ≤ _ := ENNReal.le_tsum (f := fun i => if k ≤ i then E i else 0) k
    _ = ENNReal.ofReal (s k).toReal := (ENNReal.ofReal_toReal (hsne k hk)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hsk k hk)

end StrictCompatLB.MeanField.T48ii

open StrictCompatLB.MeanField StrictCompatLB.MeanField.T48ii in
theorem solution (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (d : ℕ) (hd : 1 ≤ d)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsub : IsSubcritical d M G)
    (r : ℝ) (hr1 : 1 < r) (hr2 : r < 2 / (1 + lam))
    (ω : ℕ → ℝ) (hω : ∀ i, 1 ≤ i → 0 < ω i) (i₀ : ℕ)
    (h417 : ∀ i : ℕ, 1 ≤ i → ω (i₀ + i) = ω i₀ * r ^ i) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      (∀ N ≥ N₀, ∃ π : (Fin N → ℕ) → ℝ, IsStationary (jsqdKernel lam d M G N) π) ∧
      ∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
        (∀ N ≥ N₀, IsStationary (jsqdKernel lam d M G N) (π N)) → IsTightWeighted ω N₀ π := by
  obtain ⟨N₁, hN₁, hex⟩ := theorem_4_8_i lam hlam0 hlam1 d hd M hM G hconn hsub
  obtain ⟨N₂, hN₂, h49⟩ := lemma_4_9 lam hlam0 hlam1 d hd M hM G hconn hsub
  refine ⟨max N₁ N₂, le_trans hN₁ (le_max_left _ _), fun N hN =>
    (hex N (le_trans (le_max_left _ _) hN)).exists, fun π hπ => ?_⟩
  set ρ := (1 + lam) / 2 with hρdef
  set a := ρ / (1 - ρ) with hadef
  have hρ1 : ρ < 1 := by rw [hρdef]; linarith
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have ha0 : 0 ≤ a := div_nonneg hρ0.le (by linarith)
  have hρa : ρ = a / (1 + a) := by
    have hne : 1 - ρ ≠ 0 := by linarith
    rw [hadef]; field_simp; ring
  set x := r * ρ with hx
  have hx1 : x < 1 := by
    rw [hx, hρdef]
    have : r * ((1 + lam) / 2) < 2 / (1 + lam) * ((1 + lam) / 2) :=
      mul_lt_mul_of_pos_right hr2 (by linarith)
    rw [div_mul_div_comm, mul_comm 2 (1 + lam), div_self (by positivity)] at this
    linarith
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hωi₀ : 0 < ω i₀ := by
    have h1 := h417 1 le_rfl
    have h2 := hω (i₀ + 1) (by omega)
    rw [h1, pow_one] at h2
    exact pos_of_mul_pos_left h2 (by linarith)
  -- the dominating sequence `gR i = ω_i a ρ^{i-1}` (for `i ≥ 1`)
  set gR : ℕ → ℝ := fun i => if 1 ≤ i then ω i * (a * ρ ^ (i - 1)) else 0 with hgR
  have hgR0 : ∀ i, 0 ≤ gR i := fun i => by
    simp only [hgR]; split_ifs with h
    · exact mul_nonneg (hω i h).le (mul_nonneg ha0 (pow_nonneg hρ0.le _))
    · exact le_refl _
  set C := ω i₀ * a / (r ^ i₀ * ρ) with hC
  have hgRgeo : ∀ n, gR (n + (i₀ + 1)) = C * x ^ (n + (i₀ + 1)) := by
    intro n
    simp only [hgR, if_pos (show 1 ≤ n + (i₀ + 1) by omega)]
    have e1 : n + (i₀ + 1) = i₀ + (n + 1) := by ring
    rw [e1, h417 (n + 1) (by omega)]
    have e2 : i₀ + (n + 1) - 1 = i₀ + n := by omega
    rw [e2, hC, hx, mul_pow]
    have hr0 : r ^ i₀ ≠ 0 := pow_ne_zero _ (by linarith)
    field_simp
    ring
  have hgRs : Summable gR := by
    rw [← summable_nat_add_iff (i₀ + 1)]
    simp only [hgRgeo]
    have := (summable_geometric_of_lt_one hx0 hx1).mul_left (C * x ^ (i₀ + 1))
    refine this.congr (fun n => ?_)
    rw [pow_add]; ring
  have hite_s : ∀ j, Summable (fun i => if j ≤ i then gR i else 0) := fun j =>
    Summable.of_nonneg_of_le (fun i => by split_ifs; exact hgR0 i; exact le_refl _)
      (fun i => by split_ifs; exact le_refl _; exact hgR0 i) hgRs
  have hite_eq : ∀ j, ∑' i, (if j ≤ i then gR i else 0) = ∑' k, gR (k + j) := by
    intro j
    rw [← (hite_s j).sum_add_tsum_nat_add j]
    rw [Finset.sum_eq_zero (fun i hi => by simp only [mem_range] at hi; rw [if_neg (by omega)]),
      zero_add]
    congr 1; funext k; rw [if_pos (by omega)]
  -- the hypotheses of Lemma 4.10
  have hπprob : ∀ N ≥ max N₁ N₂, IsProbVec (π N) := fun N hN => (hπ N hN).1
  apply lemma_4_10 ω hω (max N₁ N₂) π hπprob
  · intro i _ η hη
    refine ⟨1, fun N hN => ?_⟩
    have : {z : Fin N → ℕ | 1 < |occ z i|} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [abs_of_nonneg (occ_nonneg z i)]; exact occ_le_one z i
    rw [this]
    unfold probOf
    simp [hη.le]
  · intro ε hε η hη
    have htail := tendsto_sum_nat_add gR
    obtain ⟨j₁, hj₁⟩ := (Metric.tendsto_atTop.mp htail) (ε * η) (by positivity)
    refine ⟨max j₁ 1, fun j hj => ⟨0, fun N hN => ?_⟩⟩
    have hN' : max N₁ N₂ ≤ N := le_trans (le_max_left _ _) hN
    have hπN := hπ N hN'
    have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
    have hsmall : ∑' i, (if j ≤ i then gR i else 0) < ε * η := by
      rw [hite_eq j]
      have := hj₁ j (le_trans (le_max_left _ _) hj)
      rw [Real.dist_eq, sub_zero] at this
      exact lt_of_le_of_lt (le_abs_self _) this
    have hdec := geometric_decay (π N) hπN.1 a ρ ha0 hρa
      (fun k hk => h49 N (le_trans (le_max_right _ _) hN') (π N) hπN k hk)
    -- Markov's inequality in `[0, ∞]`
    set W : (Fin N → ℕ) → ℝ := fun z => weightedTail ω j z with hW
    have hW0 : ∀ z, 0 ≤ W z := fun z => Finset.sum_nonneg (fun i hi => by
      simp only [mem_Ico] at hi
      exact mul_nonneg (hω i (by omega)).le (occ_nonneg z i))
    have hWexp : ∀ z, ENNReal.ofReal (W z) =
        ∑' i, if j ≤ i then ENNReal.ofReal (ω i) * ENNReal.ofReal (occ z i) else 0 := by
      intro z
      simp only [hW]
      unfold weightedTail
      rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => by
        simp only [mem_Ico] at hi
        exact mul_nonneg (hω i (by omega)).le (occ_nonneg z i))]
      rw [tsum_eq_sum (s := Ico j (maxLen z + 1)) (fun i hi => by
        simp only [mem_Ico, not_and_or, not_le, not_lt] at hi
        split_ifs with h
        · rcases hi with h' | h'
          · omega
          · rw [occ_zero_of z i (by omega)]; simp
        · rfl)]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [mem_Ico] at hi
      rw [if_pos hi.1, ENNReal.ofReal_mul (hω i (by omega)).le]
    set A := {z : Fin N → ℕ | ε < W z}
    have hind : ∀ z, ENNReal.ofReal (A.indicator (π N) z) ≤
        ENNReal.ofReal (π N z) * ENNReal.ofReal (W z) * ENNReal.ofReal (1 / ε) := by
      intro z
      rw [← ENNReal.ofReal_mul (hπN.1.1 z), ← ENNReal.ofReal_mul
        (mul_nonneg (hπN.1.1 z) (hW0 z))]
      apply ENNReal.ofReal_le_ofReal
      by_cases hz : z ∈ A
      · rw [Set.indicator_of_mem hz]
        simp only [A, Set.mem_setOf_eq] at hz
        have : 1 ≤ W z * (1 / ε) := by rw [mul_one_div, le_div_iff₀ hε]; linarith
        have h0 := hπN.1.1 z
        nlinarith
      · rw [Set.indicator_of_notMem hz]
        exact mul_nonneg (mul_nonneg (hπN.1.1 z) (hW0 z)) (by positivity)
    have hsumA : Summable (fun z => A.indicator (π N) z) :=
      Summable.of_nonneg_of_le (fun z => Set.indicator_nonneg (fun z _ => hπN.1.1 z) z)
        (fun z => Set.indicator_le_self' (fun z _ => hπN.1.1 z) z) hπN.1.2.summable
    have key : ENNReal.ofReal (probOf (π N) A) ≤ ENNReal.ofReal η := by
      unfold probOf
      rw [ENNReal.ofReal_tsum_of_nonneg (fun z => Set.indicator_nonneg (fun z _ => hπN.1.1 z) z)
        hsumA]
      calc ∑' z, ENNReal.ofReal (A.indicator (π N) z)
          ≤ ∑' z, ENNReal.ofReal (π N z) * ENNReal.ofReal (W z) * ENNReal.ofReal (1 / ε) :=
            ENNReal.tsum_le_tsum hind
        _ = (∑' i, if j ≤ i then ENNReal.ofReal (ω i) *
              expectENN (π N) (fun z => occ z i) else 0) * ENNReal.ofReal (1 / ε) := by
            rw [ENNReal.tsum_mul_right]
            congr 1
            simp only [hWexp]
            have e1 : ∀ z, ENNReal.ofReal (π N z) *
                (∑' i, if j ≤ i then ENNReal.ofReal (ω i) * ENNReal.ofReal (occ z i) else 0) =
                ∑' i, (if j ≤ i then ENNReal.ofReal (ω i) *
                  (ENNReal.ofReal (π N z) * ENNReal.ofReal (occ z i)) else 0) := by
              intro z
              rw [← ENNReal.tsum_mul_left]
              congr 1; funext i; split_ifs <;> ring
            simp only [e1]
            rw [ENNReal.tsum_comm]
            congr 1; funext i
            unfold expectENN
            split_ifs
            · rw [ENNReal.tsum_mul_left]
            · simp
        _ ≤ ENNReal.ofReal (∑' i, (if j ≤ i then gR i else 0)) * ENNReal.ofReal (1 / ε) := by
            gcongr
            rw [ENNReal.ofReal_tsum_of_nonneg (fun i => by split_ifs; exact hgR0 i; exact le_refl _)
              (hite_s j)]
            apply ENNReal.tsum_le_tsum
            intro i
            split_ifs with h
            · have hi1 : 1 ≤ i := le_trans hj1 h
              simp only [hgR, if_pos hi1]
              rw [ENNReal.ofReal_mul (hω i hi1).le]
              exact mul_le_mul_right (hdec i hi1) _
            · simp
        _ = ENNReal.ofReal ((∑' i, (if j ≤ i then gR i else 0)) * (1 / ε)) := by
            rw [ENNReal.ofReal_mul (tsum_nonneg (fun i => by
              split_ifs; exact hgR0 i; exact le_refl _))]
        _ ≤ ENNReal.ofReal η := by
            apply ENNReal.ofReal_le_ofReal
            rw [mul_one_div, div_le_iff₀ hε]
            linarith
    exact (ENNReal.ofReal_le_ofReal_iff hη.le).mp key

-- Prove2me | solution 1 for Sherbrooke.appendix_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T16:32:39.553036+00:00
-- url     : https://prove2.me/submissions/76490f5c-b324-4e26-a40a-940dc930ea11

import Mathlib
import Definitions.Def_Sherbrooke_lowerHull
import Definitions.Def_Sherbrooke_Cond12
import Definitions.Def_Sherbrooke_objective

set_option autoImplicit false

namespace SherbrookeAux

open Sherbrooke

/-- Every affine minorant of `Ξ` lies below the hull. -/
theorem hull_ge (Ξ : ℕ → ℝ) {a b : ℝ} (h : ∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) (m : ℕ) :
    a * (m : ℝ) + b ≤ lowerHull Ξ m := by
  unfold lowerHull
  refine le_csSup ⟨Ξ m, ?_⟩ ⟨a, b, h, rfl⟩
  rintro y ⟨a', b', h', rfl⟩
  exact h' m

/-- The hull lies below `Ξ`. -/
theorem hull_le (Ξ : ℕ → ℝ) (hb : BddBelow (Set.range Ξ)) (m : ℕ) :
    lowerHull Ξ m ≤ Ξ m := by
  unfold lowerHull
  obtain ⟨L, hL⟩ := hb
  refine csSup_le ⟨L, 0, L, fun k => ?_, by simp⟩ ?_
  · have := hL ⟨k, rfl⟩
    simpa using this
  · rintro y ⟨a, b, h, rfl⟩
    exact h m

/-- Discrete convexity of the hull. -/
theorem hull_conv (Ξ : ℕ → ℝ) (hb : BddBelow (Set.range Ξ)) (k : ℕ) :
    2 * lowerHull Ξ (k + 1) ≤ lowerHull Ξ k + lowerHull Ξ (k + 2) := by
  have hne : ({y : ℝ | ∃ a b : ℝ, (∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) ∧
      y = a * ((k + 1 : ℕ) : ℝ) + b}).Nonempty := by
    obtain ⟨L, hL⟩ := hb
    exact ⟨L, 0, L, fun j => by simpa using hL ⟨j, rfl⟩, by simp⟩
  have key : lowerHull Ξ (k + 1) ≤ (lowerHull Ξ k + lowerHull Ξ (k + 2)) / 2 := by
    unfold lowerHull at *
    refine csSup_le hne ?_
    rintro y ⟨a, b, h, rfl⟩
    have h1 := hull_ge Ξ h k
    have h2 := hull_ge Ξ h (k + 2)
    unfold lowerHull at h1 h2
    push_cast at h1 h2 ⊢
    linarith
  linarith

theorem diff_mono (Ξ : ℕ → ℝ) (hb : BddBelow (Set.range Ξ)) :
    Monotone (fun k : ℕ => lowerHull Ξ (k + 1) - lowerHull Ξ k) := by
  refine monotone_nat_of_le_succ fun k => ?_
  have := hull_conv Ξ hb k
  show lowerHull Ξ (k + 1) - lowerHull Ξ k ≤ lowerHull Ξ (k + 1 + 1) - lowerHull Ξ (k + 1)
  have e : k + 1 + 1 = k + 2 := rfl
  rw [e]
  linarith

theorem cond12_unique (c : ℝ) (Ξ : ℕ → ℝ) (hb : BddBelow (Set.range Ξ)) {m₁ m₂ : ℕ}
    (h₁ : Cond12 c Ξ m₁) (h₂ : Cond12 c Ξ m₂) : m₁ = m₂ := by
  have key : ∀ p q : ℕ, Cond12 c Ξ p → Cond12 c Ξ q → ¬ p < q := by
    intro p q hp hq hpq
    have hq0 : q ≠ 0 := by omega
    rcases hq.2 with hq' | hq'
    · exact hq0 hq'
    have hmono := diff_mono Ξ hb (show p ≤ q - 1 by omega)
    simp only at hmono
    have e : q - 1 + 1 = q := by omega
    rw [e] at hmono
    have := hp.1
    linarith
  rcases lt_trichotomy m₁ m₂ with h | h | h
  · exact absurd h (key _ _ h₁ h₂)
  · exact h
  · exact absurd h (key _ _ h₂ h₁)

/-- The item objective `k ↦ c k + Ξ k` attains its minimum. -/
theorem exists_min (c : ℝ) (Ξ : ℕ → ℝ) (hb : BddBelow (Set.range Ξ)) (hc : 0 ≤ c)
    (hcorr : 0 < c ∨ ∃ m₀ : ℕ, ∀ k : ℕ, Ξ m₀ ≤ Ξ k) :
    ∃ k : ℕ, ∀ j : ℕ, c * (k : ℝ) + Ξ k ≤ c * (j : ℝ) + Ξ j := by
  rcases hcorr with hpos | ⟨m₀, hm₀⟩
  · obtain ⟨L, hL⟩ := hb
    obtain ⟨N, hN⟩ := exists_nat_gt ((Ξ 0 - L) / c)
    obtain ⟨k, -, hk⟩ := Finset.exists_min_image (Finset.range (N + 1))
      (fun j : ℕ => c * (j : ℝ) + Ξ j) ⟨0, by simp⟩
    refine ⟨k, fun j => ?_⟩
    by_cases hj : j ≤ N
    · exact hk j (by simp; omega)
    · have h0 := hk 0 (by simp)
      have hjN : (N : ℝ) ≤ j := by exact_mod_cast (show N ≤ j by omega)
      have hLj := hL ⟨j, rfl⟩
      rw [div_lt_iff₀ hpos] at hN
      have : c * (N : ℝ) ≤ c * (j : ℝ) := mul_le_mul_of_nonneg_left hjN hc
      simp at h0
      linarith
  · obtain ⟨k, -, hk⟩ := Finset.exists_min_image (Finset.range (m₀ + 1))
      (fun j : ℕ => c * (j : ℝ) + Ξ j) ⟨0, by simp⟩
    refine ⟨k, fun j => ?_⟩
    by_cases hj : j ≤ m₀
    · exact hk j (by simp; omega)
    · have h0 := hk m₀ (by simp)
      have hjN : (m₀ : ℝ) ≤ j := by exact_mod_cast (show m₀ ≤ j by omega)
      have : c * (m₀ : ℝ) ≤ c * (j : ℝ) := mul_le_mul_of_nonneg_left hjN hc
      have := hm₀ j
      linarith

/-- The smallest minimizer of `k ↦ c k + Ξ k` satisfies condition (12). -/
theorem exists_cond12_min (c : ℝ) (Ξ : ℕ → ℝ) (hb : BddBelow (Set.range Ξ)) (hc : 0 ≤ c)
    (hcorr : 0 < c ∨ ∃ m₀ : ℕ, ∀ k : ℕ, Ξ m₀ ≤ Ξ k) :
    ∃ k : ℕ, Cond12 c Ξ k ∧ ∀ j : ℕ, c * (k : ℝ) + Ξ k ≤ c * (j : ℝ) + Ξ j := by
  classical
  have hex := exists_min c Ξ hb hc hcorr
  set ks := Nat.find hex with hks
  have hP : ∀ j : ℕ, c * (ks : ℝ) + Ξ ks ≤ c * (j : ℝ) + Ξ j := Nat.find_spec hex
  refine ⟨ks, ⟨?_, ?_⟩, hP⟩
  · -- the minorant `k ↦ -c k + g(ks)`
    have hmin : ∀ k : ℕ, (-c) * (k : ℝ) + (c * (ks : ℝ) + Ξ ks) ≤ Ξ k := by
      intro k
      have := hP k
      linarith
    have h1 := hull_ge Ξ hmin (ks + 1)
    have h2 := hull_le Ξ hb ks
    push_cast at h1
    linarith
  · by_cases hk0 : ks = 0
    · exact Or.inl hk0
    right
    have hstrict : ∀ j : ℕ, j < ks → c * (ks : ℝ) + Ξ ks < c * (j : ℝ) + Ξ j := by
      intro j hj
      have hn := Nat.find_min hex (show j < Nat.find hex from hj)
      simp only [not_forall, not_le] at hn
      obtain ⟨i, hi⟩ := hn
      have := hP i
      linarith
    obtain ⟨j₀, hj₀, hj₀min⟩ := Finset.exists_min_image (Finset.range ks)
      (fun j : ℕ => c * (j : ℝ) + Ξ j - (c * (ks : ℝ) + Ξ ks)) ⟨0, by simp; omega⟩
    set δ := c * (j₀ : ℝ) + Ξ j₀ - (c * (ks : ℝ) + Ξ ks) with hδ
    have hδpos : 0 < δ := by
      have := hstrict j₀ (by simpa using hj₀)
      rw [hδ]; linarith
    have hkpos : (0 : ℝ) < ks := by exact_mod_cast Nat.pos_of_ne_zero hk0
    set ε := δ / (ks : ℝ) with hε
    have hεpos : 0 < ε := div_pos hδpos hkpos
    have hεk : ε * (ks : ℝ) = δ := div_mul_cancel₀ δ (ne_of_gt hkpos)
    have hmin : ∀ k : ℕ, (-c - ε) * (k : ℝ) + (c * (ks : ℝ) + Ξ ks + ε * (ks : ℝ)) ≤ Ξ k := by
      intro k
      by_cases hk : ks ≤ k
      · have hkk : (ks : ℝ) ≤ k := by exact_mod_cast hk
        have := hP k
        have : ε * (ks : ℝ) ≤ ε * (k : ℝ) := mul_le_mul_of_nonneg_left hkk hεpos.le
        nlinarith
      · have hlt : k < ks := by omega
        have h1 := hj₀min k (by simpa using hlt)
        have hk0' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have : 0 ≤ ε * (k : ℝ) := mul_nonneg hεpos.le hk0'
        linarith
    have h1 := hull_ge Ξ hmin (ks - 1)
    have h2 := hull_le Ξ hb ks
    have hcast : ((ks - 1 : ℕ) : ℝ) = (ks : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk0)]; simp
    rw [hcast] at h1
    nlinarith

theorem item_opt (c : ℝ) (Ξ : ℕ → ℝ) (hb : BddBelow (Set.range Ξ)) (hc : 0 ≤ c)
    (hcorr : 0 < c ∨ ∃ m₀ : ℕ, ∀ k : ℕ, Ξ m₀ ≤ Ξ k) {mb : ℕ} (hm : Cond12 c Ξ mb) (j : ℕ) :
    c * (mb : ℝ) + Ξ mb ≤ c * (j : ℝ) + Ξ j := by
  obtain ⟨k, hk, hkmin⟩ := exists_cond12_min c Ξ hb hc hcorr
  have := cond12_unique c Ξ hb hm hk
  subst this
  exact hkmin j

end SherbrookeAux

open Sherbrooke in
theorem solution {ι : Type*} [Fintype ι] (c : ι → ℝ) (Ξ : ι → ℕ → ℝ)
    (hanti : ∀ i, Antitone (Ξ i)) (hbdd : ∀ i, BddBelow (Set.range (Ξ i)))
    (hc : ∀ i, 0 ≤ c i)
    (hcorr : ∀ i, 0 < c i ∨ ∃ m₀ : ℕ, ∀ k : ℕ, Ξ i m₀ ≤ Ξ i k) :
    (∀ i, ∃! m : ℕ, Cond12 (c i) (Ξ i) m) ∧
      ∀ mbar : ι → ℕ, (∀ i, Cond12 (c i) (Ξ i) (mbar i)) →
        ∀ m : ι → ℕ, objective c Ξ mbar ≤ objective c Ξ m := by
  refine ⟨fun i => ?_, fun mbar hm m => ?_⟩
  · obtain ⟨k, hk, -⟩ := SherbrookeAux.exists_cond12_min (c i) (Ξ i) (hbdd i) (hc i) (hcorr i)
    exact ⟨k, hk, fun y hy => SherbrookeAux.cond12_unique (c i) (Ξ i) (hbdd i) hy hk⟩
  · unfold objective
    exact Finset.sum_le_sum fun i _ =>
      SherbrookeAux.item_opt (c i) (Ξ i) (hbdd i) (hc i) (hcorr i) (hm i) (m i)

-- Prove2me | solution 1 for PeriodicMAB.Lower.fact_1_dense
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:50:47.932327+00:00
-- url     : https://prove2.me/submissions/4e66763c-f3f6-4a0a-a80c-62553f74d07d

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_GaussianBandit
import Definitions.Def_PeriodicMAB_Lower_Model

namespace PeriodicMAB.Lower

lemma fact1_bump_minPeriod (c e : ℝ) (he : e ≠ 0) (p : ℕ) (hp : 0 < p) :
    PeriodicMAB.Upper.IsMinPeriod
      (fun t => c + e * (if t % p = 1 % p then (1 : ℝ) else 0)) p := by
  refine ⟨hp, fun t _ => by simp [Nat.add_mod_right], fun q hq0 hqp h => ?_⟩
  have h1 := h 1 le_rfl
  have hp2 : 2 ≤ p := by omega
  have hmod1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  simp only [hmod1, Nat.one_mod_eq_one.mpr (by omega : p ≠ 1)] at h1
  have hne : (1 + q) % p ≠ 1 := by
    rcases Nat.lt_or_ge (1 + q) p with hl | hl
    · rw [Nat.mod_eq_of_lt hl]; omega
    · have : 1 + q = p := by omega
      rw [this, Nat.mod_self]; omega
  rw [if_neg hne] at h1
  simp at h1
  exact he h1

end PeriodicMAB.Lower

open PeriodicMAB.Lower in
theorem solution (K T : ℕ) [NeZero K] (Tper : Fin K → ℕ) (hK : 2 ≤ K)
    (hTper : ∀ k, 1 ≤ Tper k) (μ₁ : Fin K → ℕ → ℝ) (hμ₁ : InE2 T (Tper 0) μ₁)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ μ₂ : Fin K → ℕ → ℝ, InE3 T Tper μ₂ ∧ μ₂ 0 = μ₁ 0 ∧ instDist Tper μ₁ μ₂ < δ := by
  obtain ⟨hper0, hstat, hbd⟩ := hμ₁
  set S : ℝ := ∑ k, (Tper k : ℝ) with hS
  have hS0 : 0 ≤ S := by positivity
  set η : ℝ := min (1 / 2) (δ / (S + 1)) with hη
  have hηpos : 0 < η := lt_min (by norm_num) (div_pos hδ (by linarith))
  have hηle : η ≤ 1 / 2 := min_le_left _ _
  have hηle2 : η ≤ δ / (S + 1) := min_le_right _ _
  let sgn : Fin K → ℝ := fun k => if μ₁ k 1 ≤ 1 / 2 then η else -η
  have hsgn : ∀ k, sgn k ≠ 0 := fun k => by
    simp only [sgn]; split_ifs <;> [exact hηpos.ne'; exact neg_ne_zero.mpr hηpos.ne']
  refine ⟨fun k t => if k = 0 then μ₁ 0 t else
      μ₁ k 1 + sgn k * (if t % Tper k = 1 % Tper k then (1 : ℝ) else 0), ⟨?_, ?_⟩, ?_, ?_⟩
  · intro k
    by_cases hk : k = 0
    · subst hk; simpa using hper0
    · simp only [hk, if_false]
      exact fact1_bump_minPeriod _ _ (hsgn k) _ (hTper k)
  · intro k t ht1 htT
    by_cases hk : k = 0
    · subst hk; simpa using hbd 0 t ht1 htT
    · simp only [hk, if_false]
      have hc := hbd k 1 le_rfl (le_trans ht1 htT)
      obtain ⟨hc0, hc1⟩ := hc
      simp only [sgn]
      constructor <;> split_ifs <;> nlinarith
  · funext t; simp
  · unfold instDist
    rw [Real.sqrt_lt' hδ]
    have hterm : ∀ k, ∀ p ∈ Finset.Icc 1 (Tper k),
        (μ₁ k p - (if k = 0 then μ₁ 0 p else
          μ₁ k 1 + sgn k * (if p % Tper k = 1 % Tper k then (1 : ℝ) else 0))) ^ 2 ≤ η ^ 2 := by
      intro k p hp
      have hp1 : 1 ≤ p := (Finset.mem_Icc.mp hp).1
      by_cases hk : k = 0
      · subst hk; simp; positivity
      · simp only [hk, if_false, hstat k hk p hp1]
        have : (μ₁ k 1 - (μ₁ k 1 + sgn k * (if p % Tper k = 1 % Tper k then (1 : ℝ) else 0)))
            = -(sgn k * (if p % Tper k = 1 % Tper k then (1 : ℝ) else 0)) := by ring
        rw [this, neg_sq]
        simp only [sgn]
        split_ifs <;> nlinarith
    calc _ ≤ ∑ k, ∑ p ∈ Finset.Icc 1 (Tper k), η ^ 2 :=
          Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun p hp => hterm k p hp))
      _ = S * η ^ 2 := by
          simp [hS, Finset.sum_mul]
      _ < δ ^ 2 := by
          have h1 : η * (S + 1) ≤ δ := by
            rw [le_div_iff₀ (by linarith)] at hηle2; exact hηle2
          have h2 : (η * (S + 1)) ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
          have h3 : 0 < η ^ 2 := by positivity
          nlinarith [mul_nonneg h3.le hS0, mul_nonneg (mul_nonneg h3.le hS0) hS0]

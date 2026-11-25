-- Prove2me | solution 1 for UpperTheory.BernoulliSumsFrobeniusOrbits.shares_of_counts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:46:48.555375+00:00
-- url     : https://prove2.me/submissions/1a5de53a-9878-4d97-ab5e-ff086ca36ac6

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_SharesOfCounts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open Classical
namespace UpperTheory.BernoulliSumsFrobeniusOrbits
theorem _root_.solution :
    ∀ (A : Type) [Fintype A] [DecidableEq A] [AddCommGroup A] (A0 : AddSubgroup A) (T : Finset A) (δ η D : ℝ),
      0 < δ → η ≤ 1 → 0 ≤ D → 4 * A0.index * D ≤ η * (δ * Nat.card A0) →
      (∀ γ : A, |((T.filter fun t => t - γ ∈ A0).card : ℝ) - (if γ ∈ A0 then δ else 3 / 4 * δ) * Nat.card A0| ≤ D) →
      δ * Fintype.card A / 2 ≤ (T.card : ℝ) ∧ (T.card : ℝ) ≤ 2 * δ * Fintype.card A ∧
        ∀ γ : A, |((T.filter fun t => t - γ ∈ A0).card : ℝ) -
          (if γ ∈ A0 then 4 else 3) / (3 * (A0.index : ℝ) + 1) * (T.card : ℝ)| ≤ η * (T.card : ℝ) := by
  intro A _ _ _ A0 T δ η D hδ hη hD hDη hc
  set m : ℕ := A0.index with hm_def
  set n : ℕ := Nat.card A0 with hn_def
  have hm : (1:ℝ) ≤ m := by
    have h0 : A0.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
  have hn : (1:ℝ) ≤ n := by
    have h0 : 0 < Nat.card A0 := Nat.card_pos
    exact_mod_cast h0
  have hA : (Fintype.card A : ℝ) = m * n := by
    have h1 : n * m = Fintype.card A := by
      rw [hn_def, hm_def, A0.card_mul_index, Nat.card_eq_fintype_card]
    rw [← h1]
    push_cast
    ring
  have hcardA0 : (Finset.univ.filter fun x : A => x ∈ A0).card = n := by
    rw [hn_def, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsumN : ∑ γ : A, (T.filter fun t => t - γ ∈ A0).card = T.card * n := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    have inner : ∀ t : A, (∑ γ : A, if t - γ ∈ A0 then 1 else 0) = n := by
      intro t
      have h2 := Equiv.sum_comp (Equiv.subLeft t) (fun x => if x ∈ A0 then (1:ℕ) else 0)
      simp only [Equiv.subLeft_apply] at h2
      rw [h2, ← Finset.card_filter]
      exact hcardA0
    rw [Finset.sum_congr rfl (fun t _ => inner t), Finset.sum_const, smul_eq_mul]
  have hsum : (∑ γ : A, ((T.filter fun t => t - γ ∈ A0).card : ℝ)) = n * T.card := by
    have h3 := congrArg (Nat.cast : ℕ → ℝ) hsumN
    push_cast at h3
    rw [h3]
    ring
  have hf : (∑ γ : A, (if γ ∈ A0 then δ else 3 / 4 * δ) * (n:ℝ)) = (3 * m + 1) / 4 * δ * n * n := by
    have hpt : ∀ γ : A, (if γ ∈ A0 then δ else 3 / 4 * δ) * (n:ℝ)
        = 3 / 4 * δ * n + (if γ ∈ A0 then δ / 4 * n else 0) := by
      intro γ
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun γ _ => hpt γ), Finset.sum_add_distrib, ← Finset.sum_filter,
      Finset.sum_const, Finset.sum_const, hcardA0, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, hA]
    ring
  have hdiff : |(n:ℝ) * T.card - (3 * m + 1) / 4 * δ * n * n| ≤ m * n * D := by
    rw [← hsum, ← hf, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ γ : A, |((T.filter fun t => t - γ ∈ A0).card : ℝ) - (if γ ∈ A0 then δ else 3 / 4 * δ) * n| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ γ : A, D := Finset.sum_le_sum fun γ _ => hc γ
      _ = m * n * D := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hA]
  have hn0 : (0:ℝ) < n := by linarith
  have hT : |(T.card : ℝ) - (3 * m + 1) / 4 * δ * n| ≤ m * D := by
    have he : (n:ℝ) * T.card - (3 * m + 1) / 4 * δ * n * n = n * ((T.card : ℝ) - (3 * m + 1) / 4 * δ * n) := by ring
    rw [he, abs_mul, abs_of_pos hn0] at hdiff
    have h4 : (n:ℝ) * |(T.card : ℝ) - (3 * m + 1) / 4 * δ * n| ≤ n * (m * D) := by linarith
    exact le_of_mul_le_mul_left h4 hn0
  have hδn : 0 < δ * n := mul_pos hδ hn0
  have hηδ : η * (δ * n) ≤ δ * n := mul_le_of_le_one_left (le_of_lt hδn) hη
  have hmD : 0 ≤ (m:ℝ) * D := mul_nonneg (by linarith) hD
  have hmδn : 0 ≤ (m:ℝ) * (δ * n) := mul_nonneg (by linarith) (le_of_lt hδn)
  have hm1δn : 0 ≤ ((m:ℝ) - 1) * (δ * n) := mul_nonneg (by linarith) (le_of_lt hδn)
  rw [abs_le] at hT
  have hX1 : 3 * m * δ * n / 4 ≤ (T.card : ℝ) := by nlinarith
  have hη0 : 0 ≤ η := by
    by_contra hneg
    push_neg at hneg
    have h5 : η * (δ * n) < 0 := mul_neg_of_neg_of_pos hneg hδn
    linarith
  have hηX : 3 * D ≤ η * T.card := by
    have hmm : 0 ≤ D * ((m:ℝ) * m - 1) := mul_nonneg hD (by nlinarith)
    calc 3 * D ≤ 3 * m * m * D := by nlinarith
      _ = (3 * m / 4) * (4 * m * D) := by ring
      _ ≤ (3 * m / 4) * (η * (δ * n)) := mul_le_mul_of_nonneg_left hDη (by positivity)
      _ = η * (3 * m * δ * n / 4) := by ring
      _ ≤ η * T.card := mul_le_mul_of_nonneg_left hX1 hη0
  have hK : (0:ℝ) < 3 * m + 1 := by linarith
  have key : ∀ w c : ℝ, 0 ≤ w → w ≤ 4 → |c - w * δ * n / 4| ≤ D →
      |c - w / (3 * m + 1) * T.card| ≤ η * T.card := by
    intro w c hw0 hw4 hcw
    have hE : w / (3 * m + 1) * (T.card : ℝ)
        = w * δ * n / 4 + w * ((T.card : ℝ) - (3 * m + 1) / 4 * δ * n) / (3 * m + 1) := by
      field_simp
      ring
    have h1 : |w * ((T.card : ℝ) - (3 * m + 1) / 4 * δ * n) / (3 * m + 1)| ≤ 2 * D := by
      rw [abs_div, abs_mul, abs_of_nonneg hw0, abs_of_pos hK, div_le_iff₀ hK]
      have habs : |(T.card : ℝ) - (3 * m + 1) / 4 * δ * n| ≤ m * D := abs_le.mpr hT
      calc w * |(T.card : ℝ) - (3 * m + 1) / 4 * δ * n| ≤ 4 * (m * D) :=
            mul_le_mul hw4 habs (abs_nonneg _) (by norm_num)
        _ ≤ 2 * D * (3 * m + 1) := by nlinarith
    rw [hE]
    rw [abs_le] at hcw h1 ⊢
    constructor <;> linarith [hcw.1, hcw.2, h1.1, h1.2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hA]; nlinarith
  · rw [hA]; nlinarith
  · intro γ
    have hcγ := hc γ
    by_cases hγ : γ ∈ A0
    · simp only [if_pos hγ] at hcγ ⊢
      have e : (4:ℝ) * δ * n / 4 = δ * n := by ring
      exact key 4 _ (by norm_num) le_rfl (by rw [e]; exact hcγ)
    · simp only [if_neg hγ] at hcγ ⊢
      have e : (3:ℝ) * δ * n / 4 = 3 / 4 * δ * n := by ring
      exact key 3 _ (by norm_num) (by norm_num) (by rw [e]; exact hcγ)
end UpperTheory.BernoulliSumsFrobeniusOrbits

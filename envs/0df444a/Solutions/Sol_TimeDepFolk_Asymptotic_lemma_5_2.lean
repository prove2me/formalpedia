-- Prove2me | solution 1 for TimeDepFolk.Asymptotic.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:11:09.731991+00:00
-- url     : https://prove2.me/submissions/428caa9d-c996-4b7c-9081-2434ea62219b

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TDFTail

open TimeDepFolk.Asymptotic Finset

theorem summable_shift (θ : Evaluation) (n : ℕ) : Summable (fun r => θ.θ (n + r)) := by
  have := (summable_nat_add_iff n).2 θ.hasSum.summable
  simpa [add_comm] using this

theorem tail_nonneg (θ : Evaluation) (n : ℕ) : 0 ≤ ∑' r, θ.θ (n + r) :=
  tsum_nonneg fun r => θ.nonneg _

theorem cont_nonneg (θ : Evaluation) (n t : ℕ) : 0 ≤ cont θ.θ n t :=
  div_nonneg (θ.nonneg _) (tail_nonneg θ n)

theorem cont_le_zero (θ : Evaluation) (n t : ℕ) : cont θ.θ n t ≤ cont θ.θ n 0 :=
  div_le_div_of_nonneg_right (θ.antitone (by omega)) (tail_nonneg θ n)

theorem cont_antitone (θ : Evaluation) (n : ℕ) : Antitone (cont θ.θ n) :=
  fun _ _ h => div_le_div_of_nonneg_right (θ.antitone (by omega)) (tail_nonneg θ n)

theorem hasSum_cont (θ : Evaluation) (n : ℕ) (h : 0 < ∑' r, θ.θ (n + r)) :
    HasSum (cont θ.θ n) 1 := by
  have := ((summable_shift θ n).hasSum).div_const (∑' r, θ.θ (n + r))
  rwa [div_self h.ne'] at this

theorem sum_range_cont (θ : Evaluation) (n m : ℕ) :
    ∑ t ∈ range m, cont θ.θ n t = (∑ t ∈ range m, θ.θ (n + t)) / ∑' r, θ.θ (n + r) := by
  simp only [cont, Finset.sum_div]

theorem tail_split (θ : Evaluation) (n m : ℕ) :
    ∑' r, θ.θ (n + r) = ∑ r ∈ range m, θ.θ (n + r) + ∑' r, θ.θ (n + m + r) := by
  have := (summable_shift θ n).sum_add_tsum_nat_add m
  rw [← this]
  congr 1
  refine tsum_congr fun r => ?_
  congr 1; omega

end TDFTail

open TimeDepFolk.Asymptotic Finset

theorem solution (θ : Evaluation) (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) (hηκ : η < κ / 8)
    (n n' L L' S : ℕ) (hL : IsPunLength θ κ η n L) (hL' : IsPunLength θ κ η n' L')
    (hn' : n < n') (hS : n' + S = n + L) (hcase : L' < S) :
    ∑ t ∈ Finset.Ico (L' + 1) (S + 1), cont θ.θ n' t ≤ 8 * η / κ := by
  obtain ⟨d, rfl⟩ : ∃ d, n' = n + d := ⟨n' - n, by omega⟩
  have hdL : d + (S + 1) = L + 1 := by omega
  set τ := ∑' r, θ.θ (n + r) with hτ
  set τ' := ∑' r, θ.θ (n + d + r) with hτ'
  set X := ∑ t ∈ range (S + 1), θ.θ (n + d + t) with hX
  set Y := ∑ r ∈ range d, θ.θ (n + r) with hY
  have hsplit : τ = Y + τ' := TDFTail.tail_split θ n d
  have hXY : ∑ r ∈ range (L + 1), θ.θ (n + r) = Y + X := by
    rw [← hdL, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 1; omega
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun t _ => θ.nonneg _
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun t _ => θ.nonneg _
  have hpos3 : 0 < 3 * η / κ := by positivity
  have hτpos : 0 < τ := by
    rcases (TDFTail.tail_nonneg θ n).eq_or_lt with h0 | h0
    · exfalso
      have h := hL.2.1
      have hz : τ = 0 := by rw [hτ]; exact h0.symm
      rw [TDFTail.sum_range_cont] at h
      rw [show (∑' r, θ.θ (n + r)) = τ from rfl, hz, div_zero] at h
      linarith
    · exact h0
  have hlt : Y + X < 4 * η / κ * τ := by
    have h := hL.2.2
    rw [TDFTail.sum_range_cont, show (∑' r, θ.θ (n + r)) = τ from rfl, div_lt_iff₀ hτpos, hXY] at h
    exact h
  have h4 : 4 * η / κ ≤ 1 / 2 := by
    rw [div_le_iff₀ hκ]; linarith
  have hτ'big : τ / 2 ≤ τ' := by nlinarith
  have hτ'pos : 0 < τ' := by linarith
  calc ∑ t ∈ Finset.Ico (L' + 1) (S + 1), cont θ.θ (n + d) t
      ≤ ∑ t ∈ range (S + 1), cont θ.θ (n + d) t := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun t _ _ => TDFTail.cont_nonneg θ _ t
        rw [Finset.range_eq_Ico]
        exact Finset.Ico_subset_Ico (Nat.zero_le _) le_rfl
    _ = X / τ' := TDFTail.sum_range_cont θ (n + d) (S + 1)
    _ ≤ 8 * η / κ := by
        rw [div_le_iff₀ hτ'pos]
        have : X < 4 * η / κ * τ := by linarith
        have e : 8 * η / κ * τ' = 4 * η / κ * (2 * τ') := by ring
        rw [e]
        have h8 : 0 ≤ 4 * η / κ := by positivity
        nlinarith

-- Prove2me | solution 1 for TheoryOfGames.Minimax.min_max_K_pure
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:05:52.502763+00:00
-- url     : https://prove2.me/submissions/31f0779a-4d21-4f6b-ae4d-c9abbc93f67b

import Mathlib
import Definitions.Def_TheoryOfGames_Minimax_MixedStrategy

set_option autoImplicit false

namespace P8e176742

lemma isLeast_lin {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    IsLeast ((fun η : Fin n → ℝ => ∑ i, f i * η i) '' stdSimplex ℝ (Fin n)) (⨅ i, f i) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciInf_of_finite (f := f)
  refine ⟨⟨Pi.single i₀ 1, single_mem_stdSimplex ℝ i₀, ?_⟩, ?_⟩
  · show ∑ i, f i * (Pi.single i₀ (1:ℝ) : Fin n → ℝ) i = _
    rw [← hi₀]
    simp [Pi.single_apply]
  · rintro _ ⟨η, hη, rfl⟩
    have h1 : ∑ i, (⨅ j, f j) * η i = ⨅ j, f j := by rw [← Finset.mul_sum, hη.2, mul_one]
    show ⨅ j, f j ≤ ∑ i, f i * η i
    rw [← h1]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (hη.1 i)
    exact ciInf_le (Set.finite_range f).bddBelow i

lemma isGreatest_lin {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    IsGreatest ((fun η : Fin n → ℝ => ∑ i, f i * η i) '' stdSimplex ℝ (Fin n)) (⨆ i, f i) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := f)
  refine ⟨⟨Pi.single i₀ 1, single_mem_stdSimplex ℝ i₀, ?_⟩, ?_⟩
  · show ∑ i, f i * (Pi.single i₀ (1:ℝ) : Fin n → ℝ) i = _
    rw [← hi₀]
    simp [Pi.single_apply]
  · rintro _ ⟨η, hη, rfl⟩
    have h1 : ∑ i, (⨆ j, f j) * η i = ⨆ j, f j := by rw [← Finset.mul_sum, hη.2, mul_one]
    show ∑ i, f i * η i ≤ ⨆ j, f j
    rw [← h1]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (hη.1 i)
    exact le_ciSup (Set.finite_range f).bddAbove i

end P8e176742

open TheoryOfGames.Minimax in
theorem solution {β₁ β₂ : ℕ} (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) (H : Fin β₁ → Fin β₂ → ℝ) :
    (∀ ξ ∈ stdSimplex ℝ (Fin β₁),
      IsLeast (K H ξ '' stdSimplex ℝ (Fin β₂)) (⨅ τ₂, ∑ τ₁, H τ₁ τ₂ * ξ τ₁)) ∧
    (∀ η ∈ stdSimplex ℝ (Fin β₂),
      IsGreatest ((fun ξ => K H ξ η) '' stdSimplex ℝ (Fin β₁)) (⨆ τ₁, ∑ τ₂, H τ₁ τ₂ * η τ₂)) := by
  constructor
  · intro ξ _
    have hK : K H ξ = fun η : Fin β₂ → ℝ => ∑ τ₂, (∑ τ₁, H τ₁ τ₂ * ξ τ₁) * η τ₂ := by
      funext η
      unfold K
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    rw [hK]
    exact P8e176742.isLeast_lin hβ₂ _
  · intro η _
    have hK : (fun ξ => K H ξ η) = fun ξ : Fin β₁ → ℝ => ∑ τ₁, (∑ τ₂, H τ₁ τ₂ * η τ₂) * ξ τ₁ := by
      funext ξ
      unfold K
      refine Finset.sum_congr rfl fun τ₁ _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun τ₂ _ => ?_
      ring
    rw [hK]
    exact P8e176742.isGreatest_lin hβ₁ _

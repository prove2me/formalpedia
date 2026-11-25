-- Prove2me | solution 1 for Supermultiplicative.exists_nonneg_not_tendsto_rpow_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:29:07.637388+00:00
-- url     : https://prove2.me/submissions/a268e19a-9a31-4f7d-b439-877056707a2f

module
public import Definitions.Def_Fekete_Superadditive
public import Definitions.Def_Fekete_SupermultiplicativeCounterexample
public import Theorems.Thm_subadditive_neg_iff
public import Theorems.Thm_superadditive_neg_iff
attribute [local simp] subadditive_neg_iff
attribute [local simp] superadditive_neg_iff


section
@[expose] public section
open Filter Topology
namespace Supermultiplicative
private theorem evenIndicator_nonneg (n : ℕ) : 0 ≤ evenIndicator n := by
  unfold evenIndicator
  split_ifs <;> norm_num
private theorem supermultiplicative_evenIndicator : Supermultiplicative evenIndicator :=
  fun m n ↦ by
    unfold evenIndicator
    by_cases hm : Even m
    · by_cases hn : Even n
      · simp [hm, hn, hm.add hn]
      · simp only [hn, ↓reduceIte, mul_zero]
        split_ifs <;> norm_num
    · simp only [hm, ↓reduceIte, zero_mul]
      split_ifs <;> norm_num
private theorem not_tendsto_evenIndicator :
    ¬ ∃ L, Tendsto (fun n : ℕ ↦ evenIndicator n ^ (n : ℝ)⁻¹) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have h2 : Tendsto (fun k : ℕ ↦ 2 * k) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ Nat.le_mul_of_pos_left k two_pos) tendsto_id
  have h₀ := hL.comp h2
  have h₁ := hL.comp ((tendsto_add_atTop_nat 1).comp h2)
  have e₀ : ((fun n : ℕ ↦ evenIndicator n ^ (n : ℝ)⁻¹) ∘ fun k ↦ 2 * k) = fun _ ↦ 1 := by
    funext k
    simp [evenIndicator]
  have e₁ : ((fun n : ℕ ↦ evenIndicator n ^ (n : ℝ)⁻¹) ∘ (fun k ↦ k + 1) ∘ fun k ↦ 2 * k) =
      fun _ ↦ 0 := by
    funext k
    have hk : ((2 * k + 1 : ℕ) : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
    simp only [Function.comp_apply, evenIndicator, Nat.not_even_two_mul_add_one, ↓reduceIte]
    exact Real.zero_rpow hk
  rw [e₀] at h₀
  rw [e₁] at h₁
  exact one_ne_zero ((tendsto_nhds_unique tendsto_const_nhds h₀).trans
    (tendsto_nhds_unique tendsto_const_nhds h₁).symm)
end Supermultiplicative
end
end

set_option autoImplicit true
@[expose] public section
public section
open Filter Topology
open Supermultiplicative
namespace Supermultiplicative
theorem _root_.solution :
    ∃ u : ℕ → ℝ, (∀ n, 0 ≤ u n) ∧ Supermultiplicative u ∧
      ¬ ∃ L, Tendsto (fun n : ℕ ↦ u n ^ (n : ℝ)⁻¹) atTop (𝓝 L) :=
  ⟨evenIndicator, evenIndicator_nonneg, supermultiplicative_evenIndicator,
    not_tendsto_evenIndicator⟩
end Supermultiplicative

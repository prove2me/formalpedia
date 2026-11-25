-- Prove2me | solution 1 for Planks.bang
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:43:03.548743+00:00
-- url     : https://prove2.me/submissions/9bcbc114-6d47-47e1-abe0-279ad41d0020

module
public import Mathlib
public import Definitions.Def_BallPlank_Planks
public import Theorems.Thm_Planks_flip_quad

set_option autoImplicit true
@[expose] public section
public section
open scoped RealInnerProductSpace
open Classical
noncomputable section
open Planks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]
omit [FiniteDimensional ℝ E]
namespace Planks
theorem _root_.solution (ℓ : ι → E →L[ℝ] ℝ) (y : ι → E) (hy0 : ∀ i, ℓ i (y i) ≠ 0)
    (hsym : ∀ i j, ((ℓ i (y i))⁻¹) ^ 3 * ℓ i (y j) = ((ℓ j (y j))⁻¹) ^ 3 * ℓ j (y i)) :
    ∃ ε : ι → Bool, ∀ k,
      1 ≤ |ℓ k (∑ i, (sgn (ε i) * (ℓ i (y i))⁻¹) • y i)| := by
  set p : ι → ℝ := fun i => (ℓ i (y i))⁻¹ with hp
  let M : ι → ι → ℝ := fun i j => p i ^ 4 * p j * ℓ i (y j)
  have hM : ∀ i j, M i j = M j i := by
    intro i j
    have := hsym i j
    calc p i ^ 4 * p j * ℓ i (y j) = p i * p j * (p i ^ 3 * ℓ i (y j)) := by ring
      _ = p i * p j * (p j ^ 3 * ℓ j (y i)) := by rw [this]
      _ = _ := by ring
  let Q : (ι → Bool) → ℝ := fun ε => ∑ i, ∑ j, sgn (ε i) * sgn (ε j) * M i j
  obtain ⟨ε, -, hε⟩ := Finset.exists_max_image Finset.univ Q Finset.univ_nonempty
  refine ⟨ε, fun k => ?_⟩
  have hle := hε (Function.update ε k (!ε k)) (Finset.mem_univ _)
  have key := flip_quad M hM (fun i => sgn (ε i)) (fun i => sgn (Function.update ε k (!ε k) i)) k
    (by
      intro i
      by_cases h : i = k
      · subst h; simp only [Function.update_self, ite_true]; cases ε i <;> simp [sgn]
      · simp [h])
  have hz : ℓ k (∑ i, (sgn (ε i) * p i) • y i) = ∑ j, sgn (ε j) * p j * ℓ k (y j) := by
    simp [map_sum, map_smul]
  have hrow : ∑ j, sgn (ε j) * M k j = p k ^ 4 * ℓ k (∑ i, (sgn (ε i) * p i) • y i) := by
    rw [hz, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [M]; ring
  have hkk : M k k = p k ^ 4 := by
    simp only [M, hp]
    field_simp [hy0 k]
  have hsk : sgn (ε k) ^ 2 = 1 := by unfold sgn; split_ifs <;> norm_num
  have hpk : 0 < p k ^ 4 := by
    have : p k ≠ 0 := inv_ne_zero (hy0 k)
    positivity
  change ∑ i, ∑ j, _ ≤ ∑ i, ∑ j, _ at hle
  rw [key, hrow, hkk, hsk] at hle
  have h1 : 1 ≤ sgn (ε k) * ℓ k (∑ i, (sgn (ε i) * p i) • y i) := by
    nlinarith
  show 1 ≤ |ℓ k (∑ i, (sgn (ε i) * p i) • y i)|
  set w := ℓ k (∑ i, (sgn (ε i) * p i) • y i)
  cases hεk : ε k <;> simp only [sgn, hεk, ite_true, Bool.false_eq_true, ite_false] at h1
  · linarith [neg_le_abs w]
  · linarith [le_abs_self w]
end Planks

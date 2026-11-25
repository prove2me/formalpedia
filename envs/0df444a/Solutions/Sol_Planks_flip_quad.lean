-- Prove2me | solution 1 for Planks.flip_quad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:38:02.412548+00:00
-- url     : https://prove2.me/submissions/5adf1ab4-27bc-4fed-9125-d04c75156340

module
public import Mathlib
public import Definitions.Def_BallPlank_Planks

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
theorem _root_.solution (M : ι → ι → ℝ) (hM : ∀ i j, M i j = M j i) (s s' : ι → ℝ) (k : ι)
    (hs' : ∀ i, s' i = if i = k then -s k else s i) :
    ∑ i, ∑ j, s' i * s' j * M i j =
      ∑ i, ∑ j, s i * s j * M i j - 4 * s k * ∑ j, s j * M k j + 4 * s k ^ 2 * M k k := by
  have hu : ∀ i, s' i = s i + (if i = k then -2 * s k else 0) := by
    intro i; rw [hs']; by_cases h : i = k
    · subst h; simp; ring
    · simp [h]
  have hsw : ∑ i, s i * M i k = ∑ j, s j * M k j :=
    Finset.sum_congr rfl fun i _ => by rw [hM]
  have e : ∀ i j, s' i * s' j * M i j = s i * s j * M i j
      + (if i = k then -2 * s k else 0) * (s j * M i j)
      + (if j = k then -2 * s k else 0) * (s i * M i j)
      + (if i = k then -2 * s k else 0) * ((if j = k then -2 * s k else 0) * M i j) := by
    intro i j; rw [hu i, hu j]; ring
  simp only [e, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum, hsw]
  ring
end Planks

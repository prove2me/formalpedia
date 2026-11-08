-- Prove2me | solution 1 for ZeroOneExpansion.fact_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:54:02.121111+00:00
-- url     : https://prove2.me/submissions/6d6d6d81-e28f-4536-a71a-0d6e19392f79

import Mathlib
import Definitions.Def_ZeroOneExpansion_exposedFace

set_option autoImplicit false

open Matrix

namespace Aux_ZOE_fact2
open ZeroOneExpansion Matrix

theorem dot_sum {d : ℕ} (c : Fin d → ℝ) (s : Finset (Fin d → ℝ)) (w : (Fin d → ℝ) → ℝ) :
    c ⬝ᵥ (∑ x ∈ s, w x • x) = ∑ x ∈ s, w x * (c ⬝ᵥ x) := by
  rw [dotProduct_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [dotProduct_smul, smul_eq_mul]

end Aux_ZOE_fact2

open ZeroOneExpansion Matrix Aux_ZOE_fact2 in
theorem solution {d : ℕ} (X : Finset (Fin d → ℝ)) (hX : X.Nonempty) (c : Fin d → ℝ) :
    exposedFace (convexHull ℝ (X : Set (Fin d → ℝ))) (fun x => c ⬝ᵥ x) =
      convexHull ℝ {x | x ∈ X ∧ ∀ z ∈ X, c ⬝ᵥ z ≤ c ⬝ᵥ x} := by
  obtain ⟨x0, hx0, hmax⟩ := X.exists_max_image (fun x => c ⬝ᵥ x) hX
  set M := c ⬝ᵥ x0 with hM
  set Xs := X.filter (fun x => ∀ z ∈ X, c ⬝ᵥ z ≤ c ⬝ᵥ x) with hXs
  have hset : {x | x ∈ X ∧ ∀ z ∈ X, c ⬝ᵥ z ≤ c ⬝ᵥ x} = (Xs : Set (Fin d → ℝ)) := by
    ext x; simp [hXs]
  rw [hset]
  have hle : ∀ w ∈ convexHull ℝ (X : Set (Fin d → ℝ)), c ⬝ᵥ w ≤ M := by
    intro w hw
    have hconv : Convex ℝ {w : Fin d → ℝ | c ⬝ᵥ w ≤ M} := by
      have := (convex_halfSpace_le (𝕜 := ℝ) (f := fun w : Fin d → ℝ => c ⬝ᵥ w) ?_ M)
      · exact this
      · constructor
        · intro x y; exact dotProduct_add c x y
        · intro r x; simp [dotProduct_smul]
    exact convexHull_min (fun x hx => hmax x hx) hconv hw
  have heq_s : ∀ x ∈ Xs, c ⬝ᵥ x = M := by
    intro x hx
    have h := (Finset.mem_filter.mp hx)
    exact le_antisymm (hmax x h.1) (h.2 x0 hx0)
  ext y
  constructor
  · rintro ⟨hy, hymax⟩
    have hyM : c ⬝ᵥ y = M := le_antisymm (hle y hy) (hymax x0 (subset_convexHull ℝ _ hx0))
    rw [Finset.mem_convexHull] at hy
    obtain ⟨w, hw0, hw1, hyc⟩ := hy
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hyc
    simp only [id] at hyc
    -- weights vanish off Xs
    have hzero : ∀ x ∈ X, x ∉ Xs → w x = 0 := by
      have hsum : ∑ x ∈ X, w x * (M - c ⬝ᵥ x) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
        rw [← dot_sum, hyc, hyM]; ring
      have hnn : ∀ x ∈ X, 0 ≤ w x * (M - c ⬝ᵥ x) :=
        fun x hx => mul_nonneg (hw0 x hx) (by linarith [hmax x hx])
      intro x hx hxs
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum x hx
      have hlt : c ⬝ᵥ x < M := by
        rcases (hmax x hx).lt_or_eq with h | h
        · exact h
        · exfalso; apply hxs
          refine Finset.mem_filter.mpr ⟨hx, fun z hz => ?_⟩
          rw [h]; exact hmax z hz
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exfalso; linarith
    have hsub : Xs ⊆ X := Finset.filter_subset _ _
    have hw1' : ∑ x ∈ Xs, w x = 1 := by
      rw [← hw1]
      apply Finset.sum_subset hsub
      intro x hx hxs; exact hzero x hx hxs
    have hyc' : ∑ x ∈ Xs, w x • x = y := by
      rw [← hyc]
      apply Finset.sum_subset hsub
      intro x hx hxs; rw [hzero x hx hxs, zero_smul]
    rw [← hyc', ← Finset.centerMass_eq_of_sum_1 _ _ hw1']
    exact Finset.centerMass_mem_convexHull _ (fun x hx => hw0 x (hsub hx)) (by rw [hw1']; norm_num)
      (fun x hx => hx)
  · intro hy
    have hy' : y ∈ convexHull ℝ (X : Set (Fin d → ℝ)) :=
      convexHull_mono (by intro x hx; exact Finset.mem_of_mem_filter x hx) hy
    refine ⟨hy', fun w hw => ?_⟩
    have hconv : Convex ℝ {w : Fin d → ℝ | M ≤ c ⬝ᵥ w} := by
      have := (convex_halfSpace_ge (𝕜 := ℝ) (f := fun w : Fin d → ℝ => c ⬝ᵥ w) ?_ M)
      · exact this
      · constructor
        · intro x y; exact dotProduct_add c x y
        · intro r x; simp [dotProduct_smul]
    have : M ≤ c ⬝ᵥ y := convexHull_min (fun x hx => (heq_s x hx).ge) hconv hy
    simp only
    linarith [hle w hw]

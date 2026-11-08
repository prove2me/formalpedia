-- Prove2me | solution 1 for ZeroOneExpansion.fact_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:26:28.814815+00:00
-- url     : https://prove2.me/submissions/30011ad1-c692-4f4d-a13f-ee74841b9efb

import Mathlib
import Definitions.Def_ZeroOneExpansion_IsAdj

set_option autoImplicit false

open ZeroOneExpansion in
theorem solution {d : ℕ} (X : Finset (Fin d → ℝ)) (hX : X.Nonempty)
    (h01 : ∀ x ∈ X, ∀ i, x i = 0 ∨ x i = 1) :
    {x | IsVertexOf (convexHull ℝ (X : Set (Fin d → ℝ))) x} = (X : Set (Fin d → ℝ)) := by
  ext x
  simp only [Set.mem_setOf_eq, Finset.mem_coe]
  constructor
  · intro hx
    have hext := (hx : IsExposed ℝ _ {x}).isExtreme
    have : x ∈ (convexHull ℝ (X : Set (Fin d → ℝ))).extremePoints ℝ :=
      isExtreme_singleton.1 hext
    exact extremePoints_convexHull_subset this
  · intro hx
    -- the box
    have hbox : convexHull ℝ (X : Set (Fin d → ℝ)) ⊆ Set.Icc (0 : Fin d → ℝ) 1 := by
      apply convexHull_min _ (convex_Icc 0 1)
      intro z hz
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rcases h01 z hz i with h | h <;> simp [h]
      · rcases h01 z hz i with h | h <;> simp [h]
    let l : (Fin d → ℝ) →L[ℝ] ℝ := ∑ i, (2 * x i - 1) • ContinuousLinearMap.proj i
    have hl : ∀ y, l y = ∑ i, (2 * x i - 1) * y i := by
      intro y
      simp [l, ContinuousLinearMap.sum_apply]
    have hterm : ∀ y : Fin d → ℝ, y ∈ Set.Icc (0 : Fin d → ℝ) 1 → ∀ i,
        (2 * x i - 1) * y i ≤ x i := by
      intro y hy i
      have h0 := hy.1 i; have h1 := hy.2 i
      simp only [Pi.zero_apply, Pi.one_apply] at h0 h1
      rcases h01 x hx i with h | h <;> rw [h] <;> linarith
    have hlx : l x = ∑ i, x i := by
      rw [hl]
      apply Finset.sum_congr rfl
      intro i _
      rcases h01 x hx i with h | h <;> rw [h] <;> ring
    intro _
    refine ⟨l, ?_⟩
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro rfl
      refine ⟨subset_convexHull ℝ _ hx, fun z hz => ?_⟩
      rw [hl, hlx]
      exact Finset.sum_le_sum (fun i _ => hterm z (hbox hz) i)
    · rintro ⟨hy, hmax⟩
      have h1 := hmax x (subset_convexHull ℝ _ hx)
      have h2 : l y ≤ l x := by
        rw [hl, hlx]
        exact Finset.sum_le_sum (fun i _ => hterm y (hbox hy) i)
      have heq : ∑ i, (2 * x i - 1) * y i = ∑ i, x i := by
        rw [← hl, ← hlx]; linarith
      have hall := (Finset.sum_eq_sum_iff_of_le (fun i _ => hterm y (hbox hy) i)).1 heq
      funext i
      have := hall i (Finset.mem_univ i)
      rcases h01 x hx i with h | h <;> rw [h] at this ⊢ <;> linarith

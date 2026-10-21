-- Prove2me | solution 1 for OnlineLearningOCO.Winnow.lemma_2_20
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:53:51.93346+00:00
-- url     : https://prove2.me/submissions/6807ddbb-e0ae-47a9-a597-fc44375dd7c2

import Mathlib
import Definitions.Def_OnlineLearningOCO_Winnow_OMDDuality
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
open OnlineLearningOCO.Winnow

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : Set E) (R : E → ℝ) (g : E → E) (z : ℕ → E)
    (hgS : ∀ θ, g θ ∈ S)
    (hgmax : ∀ θ, ∀ w ∈ S, ⟪w, θ⟫_ℝ - R w ≤ ⟪g θ, θ⟫_ℝ - R (g θ))
    (hgrad : ∀ θ, HasGradientAt (conjOn S R) (g θ) θ) (T : ℕ) :
    (∀ u ∈ S, ∑ t ∈ range T, ⟪omdIterate g z t - u, z t⟫_ℝ ≤
        R u - R (omdIterate g z 0) +
          ∑ t ∈ range T, bregmanDiv (conjOn S R) g
            (-(∑ s ∈ range (t + 1), z s)) (-(∑ s ∈ range t, z s))) ∧
    (∀ u ∈ S, (∀ v ∈ S, R u + ∑ t ∈ range T, ⟪u, z t⟫_ℝ ≤ R v + ∑ t ∈ range T, ⟪v, z t⟫_ℝ) →
      ∑ t ∈ range T, ⟪omdIterate g z t - u, z t⟫_ℝ =
        R u - R (omdIterate g z 0) +
          ∑ t ∈ range T, bregmanDiv (conjOn S R) g
            (-(∑ s ∈ range (t + 1), z s)) (-(∑ s ∈ range t, z s))) := by
  haveI : Nonempty S := ⟨⟨g 0, hgS 0⟩⟩
  -- the conjugate is attained at g θ
  have hconj : ∀ θ, conjOn S R θ = ⟪g θ, θ⟫_ℝ - R (g θ) := by
    intro θ
    unfold conjOn
    apply le_antisymm
    · apply ciSup_le
      intro w
      exact hgmax θ w w.2
    · refine le_ciSup (f := fun w : S => ⟪(w : E), θ⟫_ℝ - R w) ?_ ⟨g θ, hgS θ⟩
      refine ⟨⟪g θ, θ⟫_ℝ - R (g θ), ?_⟩
      rintro _ ⟨w, rfl⟩
      exact hgmax θ w w.2
  have hle : ∀ θ, ∀ v ∈ S, ⟪v, θ⟫_ℝ - R v ≤ conjOn S R θ := by
    intro θ v hv
    rw [hconj]; exact hgmax θ v hv
  -- telescoped Bregman sum
  have hsum : ∑ t ∈ range T, bregmanDiv (conjOn S R) g
        (-(∑ s ∈ range (t + 1), z s)) (-(∑ s ∈ range t, z s)) =
      conjOn S R (-(∑ s ∈ range T, z s)) - conjOn S R (-(∑ s ∈ range 0, z s)) +
        ∑ t ∈ range T, ⟪omdIterate g z t, z t⟫_ℝ := by
    have : ∀ t ∈ range T, bregmanDiv (conjOn S R) g
        (-(∑ s ∈ range (t + 1), z s)) (-(∑ s ∈ range t, z s)) =
      (conjOn S R (-(∑ s ∈ range (t + 1), z s)) - conjOn S R (-(∑ s ∈ range t, z s))) +
        ⟪omdIterate g z t, z t⟫_ℝ := by
      intro t _
      unfold bregmanDiv omdIterate
      rw [sum_range_succ]
      have : -(∑ s ∈ range t, z s + z t) - -(∑ s ∈ range t, z s) = -z t := by abel
      rw [this, inner_neg_right]; ring
    rw [sum_congr rfl this, sum_add_distrib]
    congr 1
    exact sum_range_sub (fun t => conjOn S R (-(∑ s ∈ range t, z s))) T
  have hR0 : conjOn S R (-(∑ s ∈ range 0, z s)) = - R (omdIterate g z 0) := by
    rw [sum_range_zero, neg_zero, hconj]
    unfold omdIterate; simp
  have hinner : ∀ u : E, ∑ t ∈ range T, ⟪omdIterate g z t - u, z t⟫_ℝ =
      ∑ t ∈ range T, ⟪omdIterate g z t, z t⟫_ℝ - ∑ t ∈ range T, ⟪u, z t⟫_ℝ := by
    intro u
    rw [← sum_sub_distrib]
    exact sum_congr rfl (fun t _ => by rw [inner_sub_left])
  have hu_sum : ∀ u : E, ⟪u, -(∑ s ∈ range T, z s)⟫_ℝ = -∑ t ∈ range T, ⟪u, z t⟫_ℝ := by
    intro u
    rw [inner_neg_right, inner_sum]
  refine ⟨?_, ?_⟩
  · intro u hu
    rw [hinner, hsum, hR0]
    have := hle (-(∑ s ∈ range T, z s)) u hu
    rw [hu_sum] at this
    linarith
  · intro u hu hmin
    rw [hinner, hsum, hR0]
    have h1 := hle (-(∑ s ∈ range T, z s)) u hu
    rw [hu_sum] at h1
    have h2 : conjOn S R (-(∑ s ∈ range T, z s)) ≤ -∑ t ∈ range T, ⟪u, z t⟫_ℝ - R u := by
      rw [hconj]
      have hg := hmin (g (-(∑ s ∈ range T, z s))) (hgS _)
      have := hu_sum (g (-(∑ s ∈ range T, z s)))
      linarith
    linarith

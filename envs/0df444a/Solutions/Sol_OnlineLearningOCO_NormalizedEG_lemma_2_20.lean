-- Prove2me | solution 1 for OnlineLearningOCO.NormalizedEG.lemma_2_20
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:10:49.486008+00:00
-- url     : https://prove2.me/submissions/ed2cfc86-1afe-4b2b-ae67-f22e3721702b

import Mathlib
import Definitions.Def_OnlineLearningOCO_NormalizedEG_Duality
set_option autoImplicit false
open scoped RealInnerProductSpace
open OnlineLearningOCO.NormalizedEG

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : Set E) (R : E → ℝ) (g : E → E) (z : ℕ → E)
    (hgS : ∀ θ, g θ ∈ S)
    (hgmax : ∀ θ, ∀ w ∈ S, ⟪w, θ⟫ - R w ≤ ⟪g θ, θ⟫ - R (g θ))
    (hgrad : ∀ θ, HasGradientAt (fenchelConj S R) (g θ) θ)
    (T : ℕ) :
    (∀ u ∈ S,
      ∑ t ∈ Finset.range T, ⟪omdIterate g z t - u, z t⟫ ≤
        R u - R (omdIterate g z 0) +
          ∑ t ∈ Finset.range T,
            bregman (fenchelConj S R) g (-(cumSum z (t + 1))) (-(cumSum z t))) ∧
    (∀ u ∈ S,
      (∀ v ∈ S, R u + ∑ t ∈ Finset.range T, ⟪u, z t⟫ ≤ R v + ∑ t ∈ Finset.range T, ⟪v, z t⟫) →
      ∑ t ∈ Finset.range T, ⟪omdIterate g z t - u, z t⟫ =
        R u - R (omdIterate g z 0) +
          ∑ t ∈ Finset.range T,
            bregman (fenchelConj S R) g (-(cumSum z (t + 1))) (-(cumSum z t))) := by
  haveI : Nonempty S := ⟨⟨g 0, hgS 0⟩⟩
  have hconj : ∀ θ, fenchelConj S R θ = ⟪g θ, θ⟫ - R (g θ) := by
    intro θ
    unfold fenchelConj
    apply le_antisymm
    · apply ciSup_le
      intro w
      exact hgmax θ w w.2
    · refine le_ciSup (f := fun w : S => ⟪(w : E), θ⟫ - R w) ?_ ⟨g θ, hgS θ⟩
      refine ⟨⟪g θ, θ⟫ - R (g θ), ?_⟩
      rintro _ ⟨w, rfl⟩
      exact hgmax θ w w.2
  have hle : ∀ θ, ∀ v ∈ S, ⟪v, θ⟫ - R v ≤ fenchelConj S R θ := by
    intro θ v hv
    rw [hconj]; exact hgmax θ v hv
  have hcs : ∀ t, cumSum z (t + 1) = cumSum z t + z t := by
    intro t; unfold cumSum; rw [Finset.sum_range_succ]
  have hsum : ∑ t ∈ Finset.range T, bregman (fenchelConj S R) g
        (-(cumSum z (t + 1))) (-(cumSum z t)) =
      fenchelConj S R (-(cumSum z T)) - fenchelConj S R (-(cumSum z 0)) +
        ∑ t ∈ Finset.range T, ⟪omdIterate g z t, z t⟫ := by
    have : ∀ t ∈ Finset.range T, bregman (fenchelConj S R) g
        (-(cumSum z (t + 1))) (-(cumSum z t)) =
      (fenchelConj S R (-(cumSum z (t + 1))) - fenchelConj S R (-(cumSum z t))) +
        ⟪omdIterate g z t, z t⟫ := by
      intro t _
      unfold bregman omdIterate
      rw [hcs]
      have : -(cumSum z t + z t) - -(cumSum z t) = -z t := by abel
      rw [this, inner_neg_right]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_range_sub (fun t => fenchelConj S R (-(cumSum z t))) T
  have hR0 : fenchelConj S R (-(cumSum z 0)) = - R (omdIterate g z 0) := by
    have : cumSum z 0 = 0 := by simp [cumSum]
    rw [this, neg_zero, hconj]
    unfold omdIterate; rw [this, neg_zero]; simp
  have hinner : ∀ u : E, ∑ t ∈ Finset.range T, ⟪omdIterate g z t - u, z t⟫ =
      ∑ t ∈ Finset.range T, ⟪omdIterate g z t, z t⟫ - ∑ t ∈ Finset.range T, ⟪u, z t⟫ := by
    intro u
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun t _ => by rw [inner_sub_left])
  have hu_sum : ∀ u : E, ⟪u, -(cumSum z T)⟫ = -∑ t ∈ Finset.range T, ⟪u, z t⟫ := by
    intro u
    unfold cumSum
    rw [inner_neg_right, inner_sum]
  refine ⟨?_, ?_⟩
  · intro u hu
    rw [hinner, hsum, hR0]
    have := hle (-(cumSum z T)) u hu
    rw [hu_sum] at this
    linarith
  · intro u hu hmin
    rw [hinner, hsum, hR0]
    have h1 := hle (-(cumSum z T)) u hu
    rw [hu_sum] at h1
    have h2 : fenchelConj S R (-(cumSum z T)) ≤ -∑ t ∈ Finset.range T, ⟪u, z t⟫ - R u := by
      rw [hconj]
      have hg := hmin (g (-(cumSum z T))) (hgS _)
      have := hu_sum (g (-(cumSum z T)))
      linarith
    linarith

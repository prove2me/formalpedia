-- Prove2me | solution 1 for OnlineLearningOCO.FoReL.lemma_2_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:41:44.362763+00:00
-- url     : https://prove2.me/submissions/1b077e7d-d98a-452c-bc42-fc89d21868cc

import Mathlib
set_option autoImplicit false

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (σ : ℝ) (f : E → ℝ) (hf : StrongConvexOn S σ f)
    (w : E) (hwS : w ∈ S) (hwmin : ∀ v ∈ S, f w ≤ f v) :
    ∀ u ∈ S, σ / 2 * ‖u - w‖ ^ 2 ≤ f u - f w := by
  intro u hu
  have key : ∀ t : ℝ, t ∈ Set.Ioo (0:ℝ) 1 →
      (1 - t) * (σ / 2 * ‖u - w‖ ^ 2) ≤ f u - f w := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h1 := hf.2 hwS hu (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
    have h2 : f w ≤ f ((1 - t) • w + t • u) :=
      hwmin _ (hf.1 hwS hu (by linarith) ht0.le (by ring))
    have h3 : ‖w - u‖ = ‖u - w‖ := norm_sub_rev _ _
    rw [h3] at h1
    simp only [smul_eq_mul] at h1
    have h4 : t * ((1 - t) * (σ / 2 * ‖u - w‖ ^ 2)) ≤ t * (f u - f w) := by
      nlinarith
    exact le_of_mul_le_mul_left h4 ht0
  have hne : (nhdsWithin (0:ℝ) (Set.Ioo 0 1)).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_Ioo (by norm_num)]
    simp
  have hlim : Filter.Tendsto (fun t : ℝ => (1 - t) * (σ / 2 * ‖u - w‖ ^ 2))
      (nhdsWithin (0:ℝ) (Set.Ioo 0 1)) (nhds ((1 - 0) * (σ / 2 * ‖u - w‖ ^ 2))) :=
    (Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds
  have := le_of_tendsto hlim (eventually_nhdsWithin_of_forall key)
  simpa using this

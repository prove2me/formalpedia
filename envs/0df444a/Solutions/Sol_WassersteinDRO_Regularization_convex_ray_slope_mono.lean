-- Prove2me | solution 1 for WassersteinDRO.Regularization.convex_ray_slope_mono
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:46:26.785993+00:00
-- url     : https://prove2.me/submissions/346be4d4-e4d8-4b8e-8448-1161a4b6914a

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E → ℝ) (hconv : ConvexOn ℝ Set.univ ℓ)
    (y u : E) (hu : ‖u‖ = 1) (d t : ℝ) (hd : 0 < d) (hdt : d ≤ t) :
    (ℓ (y + d • u) - ℓ y) / d ≤ (ℓ (y + t • u) - ℓ y) / t := by
  have hg : ConvexOn ℝ Set.univ (fun s : ℝ => ℓ (y + s • u)) := by
    refine ⟨convex_univ, fun x _ z _ a b ha hb hab => ?_⟩
    have h := hconv.2 (Set.mem_univ (y + x • u)) (Set.mem_univ (y + z • u)) ha hb hab
    have heq : y + (a • x + b • z) • u = a • (y + x • u) + b • (y + z • u) := by
      simp only [smul_eq_mul, smul_add, add_smul, mul_smul]
      calc y + (a • x • u + b • z • u) = (a + b) • y + (a • x • u + b • z • u) := by
            rw [hab, one_smul]
        _ = _ := by rw [add_smul]; abel
    simp only
    rw [heq]
    exact h
  have := hg.secant_mono (a := 0) (x := d) (y := t) (Set.mem_univ _) (Set.mem_univ _)
    (Set.mem_univ _) hd.ne' (by linarith) hdt
  simpa using this

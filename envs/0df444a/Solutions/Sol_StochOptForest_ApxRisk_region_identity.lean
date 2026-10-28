-- Prove2me | solution 1 for StochOptForest.ApxRisk.region_identity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:47:37.148998+00:00
-- url     : https://prove2.me/submissions/b18b4948-0c0f-450d-9c59-cbdbcfb649b5

import Mathlib
import Definitions.Def_StochOptForest_ApxRisk_Model

open MeasureTheory

open StochOptForest.ApxRisk in
theorem solution {p d : ℕ} (μ : Measure (Xp p)) [IsProbabilityMeasure μ]
    (cbar : Xp p → Ed d → ℝ) (R1 R2 : Set (Xp p)) (hR1 : MeasurableSet R1)
    (hR2 : MeasurableSet R2) (hdisj : Disjoint R1 R2) (hpos1 : 0 < μ R1) (hpos2 : 0 < μ R2)
    (z : Ed d) (hint1 : IntegrableOn (fun x => cbar x z) R1 μ)
    (hint2 : IntegrableOn (fun x => cbar x z) R2 μ) :
    regionProb μ R1 * regionAvg μ cbar R1 z + regionProb μ R2 * regionAvg μ cbar R2 z
      = regionProb μ (R1 ∪ R2) * regionAvg μ cbar (R1 ∪ R2) z := by
  have key : ∀ R : Set (Xp p), 0 < μ R → ∀ c : ℝ, (μ R).toReal * ((μ R).toReal⁻¹ * c) = c := by
    intro R h c
    rw [← mul_assoc, mul_inv_cancel₀ (ENNReal.toReal_pos h.ne' (measure_ne_top μ R)).ne', one_mul]
  have hU : 0 < μ (R1 ∪ R2) := lt_of_lt_of_le hpos1 (measure_mono Set.subset_union_left)
  unfold regionProb regionAvg
  rw [key R1 hpos1, key R2 hpos2, key _ hU, setIntegral_union hdisj hR2 hint1 hint2]

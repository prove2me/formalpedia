-- Prove2me | solution 1 for SpherePacking.CohnElkies.nonnegative_weighted_nonzero_frequency_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/1b032757-0031-4df9-8636-6439501ed2a4

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped Real
open scoped SchwartzMap FourierTransform
open SpherePacking SpherePacking.CohnElkies
namespace SpherePacking.CohnElkies
theorem _root_.solution {d : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (P : PeriodicSpherePacking d)
    (D : Set (EuclideanSpace ℝ (Fin d)))
    (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0) :
    0 ≤
      ∑' m : ↥(SchwartzMap.polarIntegerLattice (d := d) P.lattice),
        (if m = (0 : ↥(SchwartzMap.polarIntegerLattice (d := d) P.lattice)) then 0
        else
          (𝓕 ⇑f m).re *
            (norm (∑' x : ↑(P.centers ∩ D),
              Complex.exp (2 * π * Complex.I *
                ⟪(x : EuclideanSpace ℝ (Fin d)),
                  (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)) := by
  refine tsum_nonneg (fun m => ?_)
  by_cases hm : m = (0 : ↥(SchwartzMap.polarIntegerLattice (d := d) P.lattice))
  · simp [hm]
  · have hf : 0 ≤ (𝓕 ⇑f m).re := by
      simpa using! hCohnElkies₂ (m : EuclideanSpace ℝ (Fin d))
    simpa [centerFourierExponentialSum, hm] using! (mul_nonneg hf (sq_nonneg (norm (centerFourierExponentialSum P D m))))
end SpherePacking.CohnElkies

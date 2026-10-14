-- Prove2me | solution 1 for ThreeSum1960614.quartic_geometry
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:19:42.113504+00:00
-- url     : https://prove2.me/submissions/b590591d-9ce5-45b8-9435-60f9b6a35fd1

import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem solution (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    0 < phiDeriv t ∧ phiDeriv t < 9 ∧
    phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint ≤ phi t := by
  have ht0 : 0 ≤ t := ht.1
  have ht2 : t ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ ht.1 ht.2 2
  have ht3 : t ^ 3 ≤ (1 / 2 : ℝ) ^ 3 := by
    exact pow_le_pow_left₀ ht.1 ht.2 3
  have hp2 : 0 ≤ t ^ 2 := sq_nonneg t
  have hp3 : 0 ≤ t ^ 3 := pow_nonneg ht.1 3
  refine ⟨?_, ?_, ?_⟩
  · dsimp [phiDeriv]
    positivity
  · dsimp [phiDeriv]
    norm_num at ht2 ht3
    nlinarith [ht.2]
  · have hfactor : phi t -
        (phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint) =
        (t - tangentPoint) ^ 2 / 100000000 *
          (72447023 + 24044466 * (t + 2 * tangentPoint) +
           12022459 * (t ^ 2 + 2 * t * tangentPoint + 3 * tangentPoint ^ 2)) := by
      dsimp [phi, phiDeriv]
      ring
    have hnonneg : 0 ≤ (t - tangentPoint) ^ 2 / 100000000 *
          (72447023 + 24044466 * (t + 2 * tangentPoint) +
           12022459 * (t ^ 2 + 2 * t * tangentPoint + 3 * tangentPoint ^ 2)) := by
      dsimp [tangentPoint]
      positivity
    linarith

#print axioms solution

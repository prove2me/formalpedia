-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCenterMemIff_weightedHomogeneousComponent_X_mul_0b047dbd7110
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:28.740515+00:00
-- url     : https://prove2.me/submissions/f84ee712-9e8e-4ba5-8e98-4e07b172e557

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterMemIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open GroundTheory.Heights₂.Heights.OrbitCenterMemIff
variable {ι : Type} [DecidableEq ι] {n : ι → ℕ}
open Classical
namespace GroundTheory.Heights₂.Heights.OrbitCenterMemIff
theorem _root_.solution (j : Coord n) (G : MvPolynomial (Coord n) ℤ)
    (e : ι → ℕ) :
    weightedHomogeneousComponent (coordDeg n) e (X j * G) =
      if coordDeg n j ≤ e then X j * weightedHomogeneousComponent (coordDeg n) (e - coordDeg n j) G
      else 0 := by
  classical
  ext m
  by_cases hj : j ∈ m.support
  · have hw : Finsupp.weight (coordDeg n) m =
        Finsupp.weight (coordDeg n) (m - Finsupp.single j 1) + coordDeg n j := by
      conv_lhs => rw [← tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr
        (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)))]
      rw [map_add, Finsupp.weight_single, one_smul]
    rw [coeff_weightedHomogeneousComponent, coeff_X_mul', if_pos hj]
    by_cases h2 : coordDeg n j ≤ e
    · rw [if_pos h2, coeff_X_mul', if_pos hj, coeff_weightedHomogeneousComponent]
      by_cases h1 : Finsupp.weight (coordDeg n) m = e
      · rw [if_pos h1, if_pos (by rw [← h1, hw, add_tsub_cancel_right])]
      · rw [if_neg h1, if_neg]
        intro h3
        exact h1 (by rw [hw, h3, tsub_add_cancel_of_le h2])
    · rw [if_neg h2, coeff_zero, if_neg]
      intro h1
      apply h2
      rw [← h1, hw]
      exact le_add_self
  · rw [coeff_weightedHomogeneousComponent, coeff_X_mul', if_neg hj, ite_self]
    by_cases h2 : coordDeg n j ≤ e
    · rw [if_pos h2, coeff_X_mul', if_neg hj]
    · rw [if_neg h2, coeff_zero]
end GroundTheory.Heights₂.Heights.OrbitCenterMemIff

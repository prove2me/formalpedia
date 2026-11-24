-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_homog_sum_zero_e8577340b774
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:56.345222+00:00
-- url     : https://prove2.me/submissions/95812ca8-6653-40a1-a3a1-4f720d0a2ac8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F : Type*} [CommRing F] (g : Polynomial ℤ) (u : F) :
    ∑ j ∈ Finset.range (g.natDegree + 1), (g.coeff j : F) * u ^ j * (0 : F) ^ (g.natDegree - j) =
      (g.leadingCoeff : F) * u ^ g.natDegree := by
  rw [Finset.sum_eq_single g.natDegree]
  · rw [Nat.sub_self, pow_zero, mul_one]
    rfl
  · intro j hj hjN
    have : 0 < g.natDegree - j :=
      Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hjN)
    rw [zero_pow this.ne', mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h
end GroundTheory.Heights₂.Heights

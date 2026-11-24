-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_homog_sum_eq_99e15293109e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:56.094869+00:00
-- url     : https://prove2.me/submissions/9731a7ec-ce18-4d9f-acbe-75733167d264

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
theorem _root_.solution {F : Type*} [Field F] (g : Polynomial ℤ) (u v : F) (hv : v ≠ 0) :
    ∑ j ∈ Finset.range (g.natDegree + 1), (g.coeff j : F) * u ^ j * v ^ (g.natDegree - j) =
      v ^ g.natDegree * Polynomial.aeval (u / v) g := by
  rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ g.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have e : v ^ g.natDegree = v ^ j * v ^ (g.natDegree - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hj']
  rw [e, zsmul_eq_mul, div_pow]
  field_simp
end GroundTheory.Heights₂.Heights

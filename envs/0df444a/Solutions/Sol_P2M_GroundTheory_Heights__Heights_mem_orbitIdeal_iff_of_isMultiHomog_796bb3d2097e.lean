-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_orbitIdeal_iff_of_isMultiHomog_796bb3d2097e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:40.279587+00:00
-- url     : https://prove2.me/submissions/6d368c28-e99b-43a7-965e-19d5b1a3eb03

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterDivSuppLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_map_d62ae25f8d4a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mConeMap_of_isMultiHomog_f3a1bcb1fd3a


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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ))
    (F : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) (hF : Geo.IsMultiHomog (ι := blockIdx n) F a) :
    F ∈ orbitIdeal x ↔ evalCone (coordVec x) F = 0 := by
  have e : eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) (flatCone x) F =
      algebraMap (coordField x) (AlgebraicClosure ℚ) (evalCone (coordVec x) F) := by
    rw [← evalCone_map]
    rfl
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ F a hF, e,
    mul_eq_zero, C_eq_zero, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
  exact or_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (X_ne_zero k))
end GroundTheory.Heights₂.Heights

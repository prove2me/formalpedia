-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_evalCone_coordVec_ne_zero_c6e0cd13558e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:52.646332+00:00
-- url     : https://prove2.me/submissions/a331b5c7-c640-4522-bf0c-16d7177dd92f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitFiniteSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitArchSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mConeMap_of_isMultiHomog_f3a1bcb1fd3a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_map_d62ae25f8d4a


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
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ)
    (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (hW : s ∉ orbitIdeal x) :
    evalCone (coordVec x) s ≠ 0 := by
  intro h
  apply hW
  have e : eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) (flatCone x) s =
      algebraMap (coordField x) (AlgebraicClosure ℚ) (evalCone (coordVec x) s) := by
    rw [← evalCone_map]
    rfl
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ s a hs, e, h,
    map_zero, map_zero, zero_mul]
end GroundTheory.Heights₂.Heights

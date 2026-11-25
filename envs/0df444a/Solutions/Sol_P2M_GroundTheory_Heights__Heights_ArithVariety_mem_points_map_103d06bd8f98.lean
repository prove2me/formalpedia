-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_map_103d06bd8f98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:15:45.566644+00:00
-- url     : https://prove2.me/submissions/380a7c86-5faa-46f3-a168-24bb6d80859d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
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
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {Ω : Type*} [Field Ω]
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights
namespace ArithVariety
theorem _root_.solution (P : ArithVariety n) (τ : AlgebraicClosure ℚ →+* ℂ)
    {x : Cone n (AlgebraicClosure ℚ)} (hx : x ∈ P.points (AlgebraicClosure ℚ)) :
    (fun k i ↦ τ (x k i)) ∈ P.points ℂ :=
  ⟨fun k hk ↦ hx.1 k (funext fun i ↦ (map_eq_zero_iff τ τ.injective).mp (congrFun hk i)),
    fun f hf ↦ by rw [evalCone_map, hx.2 f hf, map_zero]⟩
end ArithVariety
end GroundTheory.Heights₂.Heights

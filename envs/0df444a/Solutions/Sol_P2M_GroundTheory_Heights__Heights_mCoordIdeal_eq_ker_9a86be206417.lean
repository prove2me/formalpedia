-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mCoordIdeal_eq_ker_9a86be206417
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:03:15.202192+00:00
-- url     : https://prove2.me/submissions/c27af02e-92c9-45fe-aa90-38379f2ce28e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading

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
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (n)
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {Ω : Type} [Field Ω] (y : Coord n → Ω) :
    Geo.mCoordIdeal (ι := blockIdx n) y =
      RingHom.ker (eval₂Hom (Int.castRingHom (MvPolynomial ι Ω)) fun v : Coord n ↦ C (y v) * X v.1) := by
  ext f
  rw [Geo.mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker, Geo.mConeMap, aeval_def]
  rfl
end GroundTheory.Heights₂.Heights

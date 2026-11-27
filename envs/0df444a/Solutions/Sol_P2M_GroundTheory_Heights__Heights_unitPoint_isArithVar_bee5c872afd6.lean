-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_unitPoint_isArithVar_bee5c872afd6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:11:46.558627+00:00
-- url     : https://prove2.me/submissions/30b20614-6aed-49a5-a9fc-b954634e031a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_whole_isArithVar_4efb22637fdb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mCoordIdeal_unitPoint_4af6af0c0629

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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    Geo.IsArithVar (ι := blockIdx fun _ : Unit ↦ 0)
      (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) (0 + 1) := by
  rw [mCoordIdeal_unitPoint]
  exact whole_isArithVar 0
end GroundTheory.Heights₂.Heights

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_whole_isArithVar_4efb22637fdb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:53:03.568809+00:00
-- url     : https://prove2.me/submissions/60c291a3-5056-4e34-a50f-baa782b9a8b0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_isHorizontal_cfaf0a26d8e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_whole_ringKrullDim_b53d304dea6b


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
theorem _root_.solution (N : ℕ) :
    Geo.IsArithVar (ι := blockIdx fun _ : Unit ↦ N) (ArithVariety.whole fun _ : Unit ↦ N).ideal (N + 1) :=
  ⟨inferInstance, ArithVariety.isMultiProjPrime _, ArithVariety.isHorizontal _, whole_ringKrullDim N⟩
end GroundTheory.Heights₂.Heights

-- Prove2me | solution 1 for PI.HtPlacesSumWork.plOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:21:22.785793+00:00
-- url     : https://prove2.me/submissions/41aa69b4-6087-4fa6-98df-f2da061c7365

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero
import Theorems.Thm_PI_HtPlacesSumWork_addv_nonneg
import Theorems.Thm_PI_HtPlacesSumWork_addv_pos_iff
import Theorems.Thm_PI_HtPlacesSumWork_addv_isNormDiscrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HtPlacesSumWork
open IsDedekindDomain WithZero IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
variable (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
variable {O F L}
variable [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
  [FaithfulSMul O L]
namespace PI.HtPlacesSumWork
theorem _root_.solution (Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal}) :
    plOf O L Q ∈ PlacesOver O L := by
  have := Q.2
  refine ⟨addv_isNormDiscrete _, fun a => ?_⟩
  rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L a]
  refine ⟨addv_nonneg _ _, ?_⟩
  rw [plOf, addv_pos_iff, ← valPl_comap Q.1]
  rfl
end PI.HtPlacesSumWork

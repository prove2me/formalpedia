-- Prove2me | solution 1 for ReciprocityTheory.Coh.resInj_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:29:01.015324+00:00
-- url     : https://prove2.me/submissions/67b186e3-20c7-4103-b9ca-e699a15163f8

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Theorems.Thm_ReciprocityTheory_Coh_cor_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function CohomologyFunctoriality₂
universe u
namespace ReciprocityTheory.Coh
theorem _root_.solution : ResInjStatement.{u} := by
  intro R _ G _ _ _ M U _ hU hunit n x y hxy
  obtain ⟨cor, -, hcor⟩ := cor_holds R G M U hU
  have h1 := hcor n x
  have h2 := hcor n y
  rw [hxy, h2] at h1
  have h3 : (U.index : R) • x = (U.index : R) • y := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact h1.symm
  exact (hunit.smul_left_cancel).1 h3
end ReciprocityTheory.Coh

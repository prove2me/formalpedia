-- Prove2me | solution 1 for ReciprocityTheory.Coh.homogExists_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:07.659+00:00
-- url     : https://prove2.me/submissions/4867dd00-1bfd-456f-9094-104dfdf0dc7a

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
open HomogeneousCochainIso
namespace ReciprocityTheory.Coh
theorem _root_.solution : HomogExistsStatement.{u} := by
  intro R _ G _ _ _ M X _ _
  exact ⟨hcx M X, fun n => LinearEquiv.refl R _, fun n a => rfl⟩
end ReciprocityTheory.Coh

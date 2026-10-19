-- Prove2me | solution 1 for SoficGroups.SourceTopLevelCompressionFinal.exists_finitelyPresented_nonsofic_group
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/b4fb61e8-1188-4d35-bd21-b98eed684d14

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_finitelyPresented_not_sofic_of_not_sofic
import Theorems.Thm_SoficGroups_SourceTopLevelCompressionFinal_binaryLeavittElementaryGroup_not_sofic

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceTopLevelCompressionFinal
open SoficGroups.SourceTopLevelCompression
open SoficGroups.KunLiteralNineSourceFiniteModels
namespace SoficGroups.SourceTopLevelCompressionFinal
theorem _root_.solution :
    ∃ (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧ ¬ SoficGroups.Sofic G := by
  exact SoficGroups.exists_finitelyPresented_not_sofic_of_not_sofic
    binaryLeavittElementaryGroup_not_sofic
end SoficGroups.SourceTopLevelCompressionFinal

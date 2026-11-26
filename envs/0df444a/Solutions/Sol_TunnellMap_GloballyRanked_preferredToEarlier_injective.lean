-- Prove2me | solution 1 for TunnellMap.GloballyRanked.preferredToEarlier_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:56.063107+00:00
-- url     : https://prove2.me/submissions/acb67779-fae7-4895-bdd3-a82daf225283

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
omit [DecidableEq S] [DecidableEq T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) (s : S) :
    Function.Injective (I.preferredToEarlier M hM s) := by
  intro t₁ t₂ h
  apply Subtype.ext
  exact M.symm.injective (congrArg Subtype.val h)
end TunnellMap.GloballyRanked

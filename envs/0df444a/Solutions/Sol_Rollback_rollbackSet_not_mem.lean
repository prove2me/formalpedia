-- Prove2me | solution 1 for Rollback.rollbackSet_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:38.513718+00:00
-- url     : https://prove2.me/submissions/fa19a2f1-7630-4653-b30a-a2f8c15bb71f

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Reachability
import Definitions.Def_EventStructures_Family_Rollback

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open Rollback
namespace Rollback
theorem _root_.solution (c : Conf F) (e : F.Event) : e ∉ rollbackSet F c e := by
  rintro ⟨m, ⟨-, -, hem⟩, hem'⟩
  exact hem hem'
end Rollback

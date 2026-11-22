-- Prove2me | solution 1 for Rollback.rollbackSet_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:37.942859+00:00
-- url     : https://prove2.me/submissions/da2c37ea-3537-42a1-89d1-a7e44f1105c7

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Reachability
import Definitions.Def_EventStructures_Family_Rollback

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open Rollback
namespace Rollback
theorem _root_.solution (c : Conf F) (e : F.Event) : rollbackSet F c e ⊆ c.val := by
  rintro x ⟨m, ⟨-, hmc, -⟩, hxm⟩
  exact hmc hxm
end Rollback

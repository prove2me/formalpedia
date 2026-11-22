-- Prove2me | solution 1 for Stable.isRollback_rollbackConf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:16:23.209558+00:00
-- url     : https://prove2.me/submissions/cd7db7dc-f842-418a-a580-748bcf2b2212

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_Rollback
import Definitions.Def_EventStructures_Stable_Rollback
import Theorems.Thm_Rollback_rollbackSet_not_mem
import Theorems.Thm_Rollback_rollbackSet_subset
import Theorems.Thm_Rollback_subset_rollbackSet


set_option autoImplicit true
open ConfFamily Rollback
variable {L : Type*} {F : ConfFamily L}
open Stable
namespace Stable
theorem _root_.solution (hF : Coherent F) (c : Conf F) (e : F.Event) :
    isRollback F c e (rollbackConf hF c e) :=
  ⟨rollbackSet_subset F c e, rollbackSet_not_mem F c e,
   fun _ hm'c hem' _ => subset_rollbackSet F hm'c hem'⟩
end Stable

-- Prove2me | solution 1 for Stable.rollback_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:16:36.458941+00:00
-- url     : https://prove2.me/submissions/e9150a90-7187-4690-a3f0-52127690de78

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
theorem _root_.solution (hF : Coherent F) {c : Conf F} {e : F.Event} {m : Conf F}
    (h : isRollback F c e m) : m = rollbackConf hF c e :=
  Subtype.ext (Set.Subset.antisymm
    (subset_rollbackSet F h.1 h.2.1)
    (h.2.2 (rollbackConf hF c e) (rollbackSet_subset F c e) (rollbackSet_not_mem F c e)
      (subset_rollbackSet F h.1 h.2.1)))
end Stable

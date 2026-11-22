-- Prove2me | solution 1 for Stable.rollbackConf_maximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:16:15.628805+00:00
-- url     : https://prove2.me/submissions/60e89bb0-a2d1-4b23-9055-46b11ab8f038

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_Rollback
import Definitions.Def_EventStructures_Stable_Rollback
import Theorems.Thm_Rollback_subset_rollbackSet


set_option autoImplicit true
open ConfFamily Rollback
variable {L : Type*} {F : ConfFamily L}
open Stable
namespace Stable
theorem _root_.solution (hF : Coherent F) (c : Conf F) (e : F.Event)
    (m : Conf F) (hmc : m.val ⊆ c.val) (hem : e ∉ m.val) :
    m.val ⊆ (rollbackConf hF c e).val :=
  subset_rollbackSet F hmc hem
end Stable

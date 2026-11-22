-- Prove2me | solution 1 for Rollback.subset_rollbackSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:54:09.652481+00:00
-- url     : https://prove2.me/submissions/0155a7de-3373-4c88-b03e-ad1af25264de

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Reachability
import Definitions.Def_EventStructures_Family_Rollback

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open Rollback
namespace Rollback
theorem _root_.solution {c m : Conf F} {e : F.Event}
    (hmc : m.val ⊆ c.val) (hem : e ∉ m.val) : m.val ⊆ rollbackSet F c e :=
  fun _ hx => ⟨m.val, ⟨m.2, hmc, hem⟩, hx⟩
end Rollback

-- Prove2me | solution 1 for Rollback.rollback_correctness_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:13:56.291666+00:00
-- url     : https://prove2.me/submissions/e7b723ce-afb8-4478-aa45-6053ce2bc81a

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Rollback
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card
import Definitions.Def_EventStructures_Prime_Rollback
import Theorems.Thm_path_exists


set_option autoImplicit true
variable {L : Type*} (es : PES L)
open Rollback
open Configuration ConfFamily
local infix:50 " ⊢ " => enables es
namespace Rollback
theorem _root_.solution {c : Conf es} {e : es.Event}
    (cF : Finset es.Event) (hcF : ∀ x, x ∈ cF ↔ x ∈ c.1) :
    Nonempty (Path es.toFamily (rollbackFuture (es := es) c e) c) := by
  have hcfin : (c.val : Set es.Event).Finite :=
    cF.finite_toSet.subset (fun x hx => Finset.mem_coe.mpr ((hcF x).mpr hx))
  exact path_exists es.toFamily (fun x hx => hx.1) (hcfin.subset (fun x hx => hx.1))
end Rollback

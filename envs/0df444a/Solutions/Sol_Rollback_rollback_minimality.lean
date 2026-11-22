-- Prove2me | solution 1 for Rollback.rollback_minimality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:14:07.023345+00:00
-- url     : https://prove2.me/submissions/a0748b2c-7d3c-467b-971d-8c41fb5ac857

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Rollback
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card
import Definitions.Def_EventStructures_Prime_Rollback

set_option autoImplicit true
variable {L : Type*} (es : PES L)
open Rollback
open Configuration ConfFamily
local infix:50 " ⊢ " => enables es
set_option linter.unusedDecidableInType false
namespace Rollback
theorem _root_.solution [DecidableEq es.Event] {c : Conf es} {e : es.Event}
    {c' : Conf es} (_hredo : c'.1 ⊢ e) (hsafe : ∀ x ∈ c'.1, x ∉ es.future e)
    (p' : Path es.toFamily c' c) :
    (c.1 ∩ es.future e).ncard ≤ Path.length es.toFamily p' := by
  have hexec : Path.ExecList es.toFamily c' (Path.trace es.toFamily p') c :=
    Path.execList_of_path es.toFamily p'
  set tr : List es.Event := Path.trace es.toFamily p' with htr
  have htgt : c.1 = c'.1 ∪ {x | x ∈ tr} :=
    Path.execList_target_eq_union es.toFamily hexec
  have hsub_set : c.1 ∩ es.future e ⊆ ↑tr.toFinset := by
    intro x ⟨hxc, hxfut⟩
    have hx_target : x ∈ c'.1 ∪ {y | y ∈ Path.trace es.toFamily p'} := htgt ▸ hxc
    rcases hx_target with hxc' | hxt
    · exact absurd hxfut (hsafe x hxc')
    · exact List.mem_toFinset.mpr hxt
  have hFsetFin : (tr.toFinset : Set es.Event).Finite :=
    tr.toFinset.finite_toSet
  calc (c.1 ∩ es.future e).ncard
      ≤ (↑tr.toFinset : Set es.Event).ncard :=
        Set.ncard_le_ncard hsub_set hFsetFin
    _ = tr.toFinset.card := Set.ncard_coe_finset _
    _ ≤ tr.length := List.toFinset_card_le _
    _ = Path.length es.toFamily p' := rfl
end Rollback

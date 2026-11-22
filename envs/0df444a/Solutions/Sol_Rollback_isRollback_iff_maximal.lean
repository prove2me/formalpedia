-- Prove2me | solution 1 for Rollback.isRollback_iff_maximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:13:18.419103+00:00
-- url     : https://prove2.me/submissions/ce022a14-b29b-4cd9-9f35-297e84d7f3ce

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Reachability
import Definitions.Def_EventStructures_Family_Rollback

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open Rollback
namespace Rollback
theorem _root_.solution {c : Conf F} {e : F.Event} {m : Conf F} :
    isRollback F c e m ↔ m ∈ RollbackCandidates F c e ∧
      ∀ m' : Conf F, m' ∈ RollbackCandidates F c e → m.1 ⊆ m'.1 → m'.1 ⊆ m.1 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact ⟨h.1, h.2.1⟩
    · intro m' hm' hsubset
      rcases hm' with ⟨hm'sub, hm'not⟩
      exact h.2.2 m' hm'sub hm'not hsubset
  · intro h
    rcases h with ⟨hm, hmax⟩
    rcases hm with ⟨hmsub, hmnot⟩
    refine ⟨hmsub, hmnot, ?_⟩
    intro m' hm'sub hm'not hsubset
    exact hmax m' ⟨hm'sub, hm'not⟩ hsubset
end Rollback

-- Prove2me | solution 1 for RamseyLib.ramsey_three_three_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:15:54.614799+00:00
-- url     : https://prove2.me/submissions/cd662cf5-ce37-45a9-9d96-3338fe137453

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib
namespace RamseyLib
theorem _root_.solution :
    ∃ G : SimpleGraph (Fin 5), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3 := by
  refine ⟨SimpleGraph.fromRel (fun i j : Fin 5 => j = i + 1), ?_, ?_⟩
  · rw [← cliqueFinset_eq_empty_iff]; decide
  · rw [← cliqueFinset_eq_empty_iff]; decide
end RamseyLib

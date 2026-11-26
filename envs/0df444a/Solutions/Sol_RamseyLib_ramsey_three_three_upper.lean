-- Prove2me | solution 1 for RamseyLib.ramsey_three_three_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:16:54.332031+00:00
-- url     : https://prove2.me/submissions/3e549f8a-aa1a-435e-bbbc-607756bf0aca

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
public import Theorems.Thm_RamseyLib_es_finset

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib
namespace RamseyLib
theorem _root_.solution (G : SimpleGraph (Fin 6)) :
    ¬ G.CliqueFree 3 ∨ ¬ Gᶜ.CliqueFree 3 := by
  classical
  rcases es_finset G 2 2 Finset.univ (by simp [Nat.choose]) with ⟨T, -, hT⟩ | ⟨T, -, hT⟩
  · exact Or.inl fun hf => hf T hT
  · exact Or.inr fun hf => hf T hT
end RamseyLib

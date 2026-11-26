-- Prove2me | solution 1 for RamseyLib.erdos_szekeres
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:16:55.498797+00:00
-- url     : https://prove2.me/submissions/fac85845-a9fb-403f-b5d9-2c87d297240f

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
theorem _root_.solution {V : Type*} [Fintype V] (G : SimpleGraph V) (s t : ℕ) (hs : 1 ≤ s)
    (ht : 1 ≤ t) (hV : (s + t - 2).choose (s - 1) ≤ Fintype.card V) :
    ¬ G.CliqueFree s ∨ ¬ Gᶜ.CliqueFree t := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have h : (s + t).choose s ≤ (Finset.univ : Finset V).card := by
    simpa [show s + 1 + (t + 1) - 2 = s + t by omega] using hV
  rcases es_finset G s t _ h with ⟨T, -, hT⟩ | ⟨T, -, hT⟩
  · exact Or.inl fun hf => hf T hT
  · exact Or.inr fun hf => hf T hT
end RamseyLib

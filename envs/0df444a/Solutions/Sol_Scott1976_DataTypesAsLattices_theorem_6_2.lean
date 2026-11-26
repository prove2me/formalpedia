-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_6_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:25.397384+00:00
-- url     : https://prove2.me/submissions/0a40dfc1-8584-4558-9d28-7536bb52eeeb

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Classification

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega} (_hf : IsScottContinuous f)
    (hval : ∀ x, f x = botElem ∨ f x = topElem) :
    {x | f x = botElem} = {x | 0 ∈ f x}ᶜ := by
  ext x
  constructor
  · intro hx hn
    have hfx : f x = botElem := hx
    have hn' : 0 ∈ f x := hn
    rw [hfx] at hn'
    exact hn'
  · intro hx
    rcases hval x with h | h
    · exact h
    · have : 0 ∈ f x := by rw [h]; exact Set.mem_univ 0
      exact (hx this).elim
end Scott1976.DataTypesAsLattices

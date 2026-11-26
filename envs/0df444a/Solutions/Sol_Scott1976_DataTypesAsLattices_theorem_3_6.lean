-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_3_6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:10.143883+00:00
-- url     : https://prove2.me/submissions/0ba5eb31-75b0-4816-95f2-54672057204a

import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
import Definitions.Def_Scott1976_DataTypesAsLattices_Enumeration

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (a : Pomega) :
    (∀ u ∈ RE, funOf u a ∈ Deg a) ∧
      (∀ x y, x ∈ Deg a → y ∈ Deg a →
        ∃ r s, IsCombinatory r ∧ IsCombinatory s ∧
          x = funOf r a ∧ y = funOf s a) := by
  constructor
  · intro u hu
    exact ⟨u, hu, rfl⟩
  · intro x y hx hy
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨r, s, hr, hs, rfl, rfl⟩
end Scott1976.DataTypesAsLattices

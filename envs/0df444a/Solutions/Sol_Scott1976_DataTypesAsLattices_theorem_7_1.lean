-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_7_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:02.038661+00:00
-- url     : https://prove2.me/submissions/85922bd0-0905-4797-b57b-c306476e01e0

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (A B : RestrictedEquiv) :
    (∀ f, (arrowE A B).mem f →
        f = graph (fun x => funOf f x) ∧
          ∀ x y, A.rel x y → B.rel (funOf f x) (funOf f y)) ∧
      (∀ u, (prodE A B).mem u →
        A.mem (funOf u (ofNat 0)) ∧ B.mem (funOf u (ofNat 1))) ∧
      (∀ u, (sumE A B).mem u →
        (u = pairElem (ofNat 0) (funOf u (ofNat 1)) ∧
          A.mem (funOf u (ofNat 1))) ∨
        (u = pairElem (ofNat 1) (funOf u (ofNat 1)) ∧
          B.mem (funOf u (ofNat 1)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    exact ⟨hf.1, fun x y hxy => hf.2.2 x y hxy⟩
  · intro u hu
    exact ⟨hu.1, hu.2⟩
  · intro u hu
    rcases hu with ⟨hu, _, hA⟩ | ⟨hu, _, hB⟩
    · exact Or.inl ⟨hu, hA⟩
    · exact Or.inr ⟨hu, hB⟩
end Scott1976.DataTypesAsLattices

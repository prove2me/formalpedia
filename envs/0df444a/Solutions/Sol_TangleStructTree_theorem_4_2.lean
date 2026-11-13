-- Prove2me | solution 1 for TangleStructTree.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:45:12.255255+00:00
-- url     : https://prove2.me/submissions/74c33dcd-b6ae-4d93-8c6a-e0f713a65f53

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_IsTrivial
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_IsStandard
import Definitions.Def_TangleStructTree_IsOrderFunction
import Definitions.Def_TangleStructTree_OrderInjective
import Definitions.Def_TangleStructTree_StronglyEfficient
import Definitions.Def_TangleStructTree_IsRich
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_Consistent
import Definitions.Def_TangleStructTree_SepTree_IsTST
import Definitions.Def_TangleStructTree_SepTree_ThoroughlyOrdered
import Theorems.Thm_TangleStructTree_theorem_4_6
import Theorems.Thm_TangleStructTree_lemma_4_7
import Theorems.Thm_TangleStructTree_theorem_4_8

section
set_option autoImplicit false

namespace TangleStructTree
open SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

theorem chk_theorem_4_2 (ord : E → ℝ) (hord : IsOrderFunction ord) (ℱ : Set (Set E))
    (hstd : IsStandard ℱ) :
    (Finite E → IsRich ord ℱ → ∃ T : SepTree E, T.ThoroughlyOrdered ord ∧ T.IsTST ℱ) ∧
      (OrderInjective ord → ∀ T T' : SepTree E, T.ThoroughlyOrdered ord → T.IsTST ℱ →
        T'.ThoroughlyOrdered ord → T'.IsTST ℱ → T = T') ∧
      (OrderInjective ord → (∃ T : SepTree E, T.ThoroughlyOrdered ord ∧ T.IsTST ℱ) →
        IsRich ord ℱ) := by
  refine ⟨fun hf hr => ?_, fun hinj T T' a b c d =>
    (TangleStructTree.theorem_4_8 ord hord hinj ℱ hstd).2.2 T T' a b c d,
    fun hinj h => TangleStructTree.lemma_4_7 ord hord hinj ℱ h⟩
  haveI := hf
  exact TangleStructTree.theorem_4_6 ord hord ℱ hr hstd

end TangleStructTree
end

theorem solution : type_of% @TangleStructTree.chk_theorem_4_2 := @TangleStructTree.chk_theorem_4_2

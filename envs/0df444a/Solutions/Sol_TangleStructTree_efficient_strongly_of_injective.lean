-- Prove2me | solution 1 for TangleStructTree.efficient_strongly_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:32:19.472725+00:00
-- url     : https://prove2.me/submissions/5f347827-48d6-484e-abcd-4176bc119dcf

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_IsOrderFunction
import Definitions.Def_TangleStructTree_OrderInjective
import Definitions.Def_TangleStructTree_StronglyEfficient

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TangleStructTree.Dev.Base

open TangleStructTree SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

end TangleStructTree.Dev.Base
end

section
set_option autoImplicit false

namespace TangleStructTree
open SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

theorem chk_efficient_strongly_of_injective (ord : E → ℝ) (hord : IsOrderFunction ord)
    (hinj : OrderInjective ord) (τ σ : Set E) (hτ : IsPartialOrientation τ)
    (hσ : Efficient ord σ τ) :
    StronglyEfficient ord σ τ := by
  refine ⟨hσ.1, fun x hx y hy hyx ⟨hlt, hle⟩ => ?_⟩
  have hxτ := hσ.1 hx
  rcases lt_or_eq_of_le hle with hl | he
  · exact hσ.2 x hx y hy hyx ⟨hlt, hl⟩
  · rcases hinj y x he with h | h
    · exact hyx h.symm
    · have hyr : y = rev x := by rw [h, rev_rev]
      have hy' : rev x ∈ τ := by rw [← hyr]; exact hy
      exact hyx (hyr.trans (hτ x hxτ hy'))

end TangleStructTree
end

theorem solution : type_of% @TangleStructTree.chk_efficient_strongly_of_injective := @TangleStructTree.chk_efficient_strongly_of_injective

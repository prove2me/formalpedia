-- Prove2me | solution 1 for TangleStructTree.theorem_4_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:45:12.070909+00:00
-- url     : https://prove2.me/submissions/0db7275c-0c41-4e96-b32b-2efa3d042095

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_IsOrderFunction
import Definitions.Def_TangleStructTree_OrderInjective
import Definitions.Def_TangleStructTree_SepTree_Consistent
import Definitions.Def_TangleStructTree_SepTree_IsTST
import Definitions.Def_TangleStructTree_SepTree_ThoroughlyOrdered
import Definitions.Def_TangleStructTree_IsTrivial
import Definitions.Def_TangleStructTree_IsStandard
import Definitions.Def_TangleStructTree_StronglyEfficient
import Definitions.Def_TangleStructTree_IsRich
import Theorems.Thm_TangleStructTree_theorem_4_6
import Theorems.Thm_TangleStructTree_lemma_4_7

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

namespace TangleStructTree.Dev.Uniq

open TangleStructTree SepSystem TangleStructTree.Dev.Base

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma nodes_sub (ord : E → ℝ) (hinj : OrderInjective ord) (ℱ : Set (Set E))
    (T T' : SepTree E) (h1 : T.ThoroughlyOrdered ord) (h2 : T.IsTST ℱ)
    (h1' : T'.ThoroughlyOrdered ord) (h2' : T'.IsTST ℱ) :
    ∀ v, v ∈ T.nodes → v ∈ T'.nodes := by
  intro v
  induction v with
  | nil => intro _; exact T'.root_mem
  | cons x u ih =>
    intro hx
    have hu := T.parent_mem x u hx
    have hu' := ih hu
    obtain ⟨hno, hmin⟩ := h1 u x hx
    have hex : ∃ y, y :: u ∈ T'.nodes := by
      by_contra hne
      push_neg at hne
      rcases h2'.2.1 u ⟨hu', hne⟩ with ⟨-, ht⟩ | ⟨-, hf⟩
      · exact hno (ht.1 x).1 |>.elim
      · exact hf (h2.2.2 u x hx)
    obtain ⟨y, hy⟩ := hex
    obtain ⟨hnoy, hminy⟩ := h1' u y hy
    have hxy : ord x = ord y := le_antisymm (hmin y hnoy) (hminy x hno)
    obtain ⟨s, hs, -⟩ := T'.split u hu' ⟨y, hy⟩
    have hys := (hs y).mp hy
    rw [hs]
    rcases hinj x y hxy with h | h
    · rcases hys with h' | h'
      · left; exact h.symm.trans h'
      · right; exact h.symm.trans h'
    · have hx' : x = rev y := by rw [h, rev_rev]
      rcases hys with h' | h'
      · right; rw [hx', h']
      · left; rw [hx', h', rev_rev]

end TangleStructTree.Dev.Uniq

namespace TangleStructTree
open SepSystem TangleStructTree.Dev.Uniq

variable {E : Type*} [PartialOrder E] [SepSystem E]

theorem uniq_aux (ord : E → ℝ) (hinj : OrderInjective ord) (ℱ : Set (Set E))
    (T T' : SepTree E) (h1 : T.ThoroughlyOrdered ord) (h2 : T.IsTST ℱ)
    (h1' : T'.ThoroughlyOrdered ord) (h2' : T'.IsTST ℱ) : T = T' := by
  have hs1 := nodes_sub ord hinj ℱ T T' h1 h2 h1' h2'
  have hs2 := nodes_sub ord hinj ℱ T' T h1' h2' h1 h2
  have : T.nodes = T'.nodes := Finset.Subset.antisymm (fun v hv => hs1 v hv) (fun v hv => hs2 v hv)
  cases T; cases T'
  simp only at this
  subst this
  rfl

end TangleStructTree
end

section
set_option autoImplicit false

namespace TangleStructTree
open SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

theorem chk_theorem_4_8 (ord : E → ℝ) (hord : IsOrderFunction ord) (hinj : OrderInjective ord)
    (ℱ : Set (Set E)) (hstd : IsStandard ℱ) :
    (Finite E → IsRich ord ℱ → ∃ T : SepTree E, T.ThoroughlyOrdered ord ∧ T.IsTST ℱ) ∧
      ((∃ T : SepTree E, T.ThoroughlyOrdered ord ∧ T.IsTST ℱ) → IsRich ord ℱ) ∧
      ∀ T T' : SepTree E, T.ThoroughlyOrdered ord → T.IsTST ℱ →
        T'.ThoroughlyOrdered ord → T'.IsTST ℱ → T = T' := by
  refine ⟨fun hf hr => ?_, fun h => TangleStructTree.lemma_4_7 ord hord hinj ℱ h,
    fun T T' a b c d => uniq_aux ord hinj ℱ T T' a b c d⟩
  haveI := hf
  exact TangleStructTree.theorem_4_6 ord hord ℱ hr hstd

end TangleStructTree
end

theorem solution : type_of% @TangleStructTree.chk_theorem_4_8 := @TangleStructTree.chk_theorem_4_8

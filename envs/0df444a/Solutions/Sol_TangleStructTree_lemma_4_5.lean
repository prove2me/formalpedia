-- Prove2me | solution 1 for TangleStructTree.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:45:12.034669+00:00
-- url     : https://prove2.me/submissions/510a80ad-679b-44bc-8ad0-50e269833885

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_ThoroughlyOrdered
import Theorems.Thm_TangleStructTree_closure_eq
import Definitions.Def_TangleStructTree_IsTrivial
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_IsStandard
import Definitions.Def_TangleStructTree_IsOrderFunction
import Definitions.Def_TangleStructTree_StronglyEfficient
import Definitions.Def_TangleStructTree_IsRich
import Definitions.Def_TangleStructTree_OrderInjective
import Definitions.Def_TangleStructTree_SepTree_Consistent
import Definitions.Def_TangleStructTree_SepTree_IsTST
import Theorems.Thm_TangleStructTree_lemma_2_2
import Theorems.Thm_TangleStructTree_lemma_4_2

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TangleStructTree.Dev.Base

open TangleStructTree SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma rev_lt_rev {x y : E} (h : x < y) : rev y < rev x := by
  refine lt_of_le_of_ne (SepSystem.rev_le_rev _ _ h.le) ?_
  intro h'
  have := congrArg rev h'
  rw [rev_rev, rev_rev] at this
  exact h.ne this.symm

lemma pairwise_path (T : SepTree E) :
    ∀ v ∈ T.nodes, v.Pairwise (fun a b => a ≠ b ∧ a ≠ rev b) := by
  intro v
  induction v with
  | nil => intro _; exact List.Pairwise.nil
  | cons x u ih =>
    intro h
    have hu := T.parent_mem x u h
    refine List.pairwise_cons.mpr ⟨?_, ih hu⟩
    obtain ⟨s, hs, hy⟩ := T.split u hu ⟨x, h⟩
    intro y hy'
    have hxs := (hs x).mp h
    obtain ⟨h1, h2⟩ := hy y hy'
    rcases hxs with rfl | rfl
    · exact ⟨fun h => h1 h.symm, fun h => h2 (by rw [h, rev_rev])⟩
    · refine ⟨fun h => h2 h.symm, fun h => h1 ?_⟩
      have := congrArg rev h
      simp only [rev_rev] at this
      exact this.symm

/-- the labels on a path are pairwise distinct and never inverse to each other -/
lemma labels_ne (T : SepTree E) {v : List E} (hv : v ∈ T.nodes) {a b : E}
    (ha : a ∈ labels v) (hb : b ∈ labels v) (hab : a ≠ b) : a ≠ rev b := by
  have := pairwise_path T v hv
  obtain ⟨l1, l2, h1⟩ := List.append_of_mem (show a ∈ v from ha)
  have hb' : b ∈ l1 ++ a :: l2 := h1 ▸ (show b ∈ v from hb)
  rw [h1] at this
  rw [List.pairwise_append] at this
  obtain ⟨hp1, hp2, hp3⟩ := this
  rw [List.pairwise_cons] at hp2
  rcases List.mem_append.mp hb' with hb1 | hb2
  · exact fun h => (hp3 b hb1 a (by simp)).2 (by rw [h, rev_rev])
  · rcases List.mem_cons.mp hb2 with rfl | hb3
    · exact absurd rfl hab
    · exact fun h => (hp2.1 b hb3).2 h

end TangleStructTree.Dev.Base
end

section
set_option autoImplicit false

namespace TangleStructTree.Dev.Cl

open TangleStructTree SepSystem TangleStructTree.Dev.Base

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma mem_cl (τ : Set E) (hτ : IsConsistent τ) {x : E} :
    x ∈ sepClosure τ ↔ x ∈ τ ∨ ∃ r ∈ τ, (r ≠ x ∧ r ≠ rev x) ∧ r < x := by
  rw [(TangleStructTree.closure_eq τ hτ).2]
  simp [Set.mem_union]

end TangleStructTree.Dev.Cl
end

section
set_option autoImplicit false

namespace TangleStructTree.Dev.L45

open TangleStructTree SepSystem TangleStructTree.Dev.Base TangleStructTree.Dev.Cl

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma cl_orientation (T : SepTree E) (v : List E) (hv : v ∈ T.nodes)
    (hcons : IsConsistent (labels v)) (hco : ∀ x ∈ labels v, ¬ IsTrivial (rev x))
    (horient : ∀ x : E, Orients (sepClosure (labels v)) x) :
    IsOrientation (sepClosure (labels v)) := by
  have h22 := TangleStructTree.lemma_2_2 (labels v) hcons hco
  intro x
  refine ⟨horient x, fun hx hrx => ?_⟩
  by_cases hxβ : x ∈ labels v <;> by_cases hrβ : rev x ∈ labels v
  · by_contra hne
    exact labels_ne T hv hxβ hrβ (fun h => hne h.symm) (by rw [rev_rev])
  · -- x ∈ β, rev x ∈ cl \ β
    exfalso
    obtain ⟨r, hr, ⟨h1, h2⟩, hlt⟩ := ((mem_cl _ hcons).mp hrx).resolve_left hrβ
    have := rev_lt_rev hlt
    rw [rev_rev] at this
    rw [rev_rev] at h2
    exact hcons x hxβ r hr h2 h1 this.le
  · exfalso
    obtain ⟨r, hr, ⟨h1, h2⟩, hlt⟩ := ((mem_cl _ hcons).mp hx).resolve_left hxβ
    have := rev_lt_rev hlt
    exact hcons (rev x) hrβ r hr h2 (by rw [rev_rev]; exact h1) this.le
  · exact h22.2 x ⟨hx, hxβ⟩ ⟨hrx, hrβ⟩

end TangleStructTree.Dev.L45

namespace TangleStructTree
open SepSystem TangleStructTree.Dev.L45

variable {E : Type*} [PartialOrder E] [SepSystem E]

theorem chk_lemma_4_5 (ord : E → ℝ) (hord : IsOrderFunction ord) (ℱ : Set (Set E))
    (hrich : IsRich ord ℱ) (hstd : IsStandard ℱ) (T : SepTree E) (hT : T.ThoroughlyOrdered ord)
    (v : List E) (hv : v ∈ T.nodes) (hcons : IsConsistent (labels v))
    (havoid : Avoids ℱ (labels v)) (horient : ∀ x : E, Orients (sepClosure (labels v)) x) :
    IsTangle ℱ (sepClosure (labels v)) := by
  have hco : ∀ x ∈ labels v, ¬ IsTrivial (rev x) := by
    intro x hx htriv
    have := hstd _ htriv
    rw [rev_rev] at this
    exact havoid _ this (by simpa using hx)
  have hor := cl_orientation T v hv hcons hco horient
  have h22 := TangleStructTree.lemma_2_2 (labels v) hcons hco
  refine ⟨hor, h22.1, fun σ hσ hsub => ?_⟩
  obtain ⟨σ', hσ', hse⟩ := hrich _ hor h22.1 (fun h => h σ hσ hsub)
  exact havoid σ' hσ' ((TangleStructTree.lemma_4_2 ord hord T hT v hv).1 σ' hse)

end TangleStructTree
end

theorem solution : type_of% @TangleStructTree.chk_lemma_4_5 := @TangleStructTree.chk_lemma_4_5

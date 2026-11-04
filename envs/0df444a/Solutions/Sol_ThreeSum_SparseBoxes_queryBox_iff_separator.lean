-- Prove2me | solution 1 for ThreeSum.SparseBoxes.queryBox_iff_separator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:56.863555+00:00
-- url     : https://prove2.me/submissions/57635b2c-a534-4ba6-8f7a-84aff52f0ea1

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SparseBoxes

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (q u leaf : Finset α) (huq : u ⊆ q) :
    QueryBox q u leaf ↔
      leaf ⊆ q ∧ u ⊆ q \ leaf ∧
        ∀ a ∈ u, ∀ x ∈ q \ leaf, x ∉ u → x < a := by
  constructor
  · rintro ⟨hleaf, hrequired⟩
    refine ⟨hleaf.trans Finset.sdiff_subset, ?_, ?_⟩
    · intro a hau
      refine Finset.mem_sdiff.mpr ⟨huq hau, ?_⟩
      intro hal
      exact (Finset.mem_sdiff.mp (hleaf hal)).2 hau
    · intro a hau x hxm hxu
      have hxf : x ∈ q \ u :=
        Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hxm).1, hxu⟩
      have hxFree : x ∈ queryFree q u := by
        by_contra hn
        have hxl := hrequired (Finset.mem_sdiff.mpr ⟨hxf, hn⟩)
        exact (Finset.mem_sdiff.mp hxm).2 hxl
      exact (Finset.mem_filter.mp hxFree).2 a hau
  · rintro ⟨hlq, hum, ho⟩
    refine ⟨?_, ?_⟩
    · intro x hxl
      refine Finset.mem_sdiff.mpr ⟨hlq hxl, ?_⟩
      intro hxu
      exact (Finset.mem_sdiff.mp (hum hxu)).2 hxl
    · intro x hx
      obtain ⟨hxf, hxn⟩ := Finset.mem_sdiff.mp hx
      by_contra hxl
      apply hxn
      apply Finset.mem_filter.mpr
      refine ⟨hxf, ?_⟩
      intro a hau
      exact ho a hau x
        (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hxf).1, hxl⟩)
        (Finset.mem_sdiff.mp hxf).2
end ThreeSum.SparseBoxes

-- Prove2me | solution 1 for SoficGroups.tableGenerator_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/dbdc1049-c64c-4085-97b4-72244256e16e

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) {g h : G} (hg : g ∈ F) (hh : h ∈ F) :
    tableGenerator F h₁ ⟨g, mem_multiplicationTable_of_mem hg⟩ *
      tableGenerator F h₁ ⟨h, mem_multiplicationTable_of_mem hh⟩ =
    tableGenerator F h₁ ⟨g * h, mul_mem_multiplicationTable hg hh⟩ := by
  classical
  have hrel :
      (FreeGroup.of ⟨g, mem_multiplicationTable_of_mem hg⟩ *
        FreeGroup.of ⟨h, mem_multiplicationTable_of_mem hh⟩) *
          (FreeGroup.of ⟨g * h, mul_mem_multiplicationTable hg hh⟩)⁻¹ ∈
        (tableRelators F h₁ : Set (FreeGroup ↥(multiplicationTable F))) := by
    change _ ∈ tableRelators F h₁
    rw [tableRelators]
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨(⟨g, hg⟩, ⟨h, hh⟩), ?_, rfl⟩
    simp
  simpa only [tableGenerator, PresentedGroup.of, map_mul] using
    PresentedGroup.mk_eq_mk_of_mul_inv_mem hrel
end SoficGroups

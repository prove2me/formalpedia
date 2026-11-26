-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_1_5_extends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:27.355958+00:00
-- url     : https://prove2.me/submissions/80189048-4256-4c10-9799-01cb9a452558

import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Basic
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_extend
import Theorems.Thm_Scott1976_DataTypesAsLattices_isOpen_memOpen


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
open TopologicalSpace
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (hf : Continuous f) (x : X) :
    extend (Y := Y) (X := X) f ↑x = f x := by
  apply subset_antisymm
  · intro k hk
    obtain ⟨U, _, hxU, hall⟩ := (mem_extend f).mp hk
    exact hall x hxU
  · intro k hk
    have hpre : IsOpen (f ⁻¹' memOpen k) :=
      IsOpen.preimage hf (isOpen_memOpen k)
    obtain ⟨U, hU, hrel⟩ := isOpen_induced_iff.mp hpre
    refine (mem_extend f).mpr ⟨U, hU, ?_, ?_⟩
    · have : x ∈ Subtype.val ⁻¹' U := by
        rwa [hrel]
      exact this
    · intro z hz
      have : z ∈ f ⁻¹' memOpen k := by
        rwa [← hrel]
      exact this
end Scott1976.DataTypesAsLattices

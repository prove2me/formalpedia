-- Prove2me | solution 1 for Scott1972.ContinuousLattice.continuous_eq_sSup_openInfs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:32:35.686989+00:00
-- url     : https://prove2.me/submissions/b4a156d0-496f-478b-9970-eab550f6ddff

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLattice_sSup_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le_trans
import Theorems.Thm_Scott1972_ContinuousLattice_isOpen_iff_scottOpen
import Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_wayBelow


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]
namespace Scott1972.ContinuousLattice
theorem _root_.solution (hE : IsContinuousLattice E) {f' : Y → E}
    (hf' : @Continuous Y E _ scottTopologicalSpace f') (y : Y) :
    f' y = sSup {d | ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ d = sInf (f' '' U)} := by
  apply le_antisymm
  · rw [← hE.sSup_wayBelow (f' y)]
    refine sSup_le fun a ha => ?_
    have hWopen : @IsOpen E scottTopologicalSpace {z : E | a ≪ z} :=
      isOpen_iff_scottOpen.mpr (scottOpen_wayBelow a)
    have hpre : IsOpen (f' ⁻¹' {z : E | a ≪ z}) := continuous_def.mp hf' _ hWopen
    have hyU : y ∈ f' ⁻¹' {z : E | a ≪ z} := ha
    refine le_trans ?_ (le_sSup ⟨f' ⁻¹' {z : E | a ≪ z}, hpre, hyU, rfl⟩)
    refine le_sInf ?_
    rintro w ⟨z, hzU, rfl⟩
    exact (hzU : a ≪ f' z).le
  · refine sSup_le ?_
    rintro d ⟨U, _hUo, hyU, rfl⟩
    exact sInf_le ⟨y, hyU, rfl⟩
end Scott1972.ContinuousLattice

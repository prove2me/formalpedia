-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottExtend_eq_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:32:29.244805+00:00
-- url     : https://prove2.me/submissions/7461d0e5-7c71-4613-a650-67fddd79a8b3

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
theorem _root_.solution (hE : IsContinuousLattice E) (e : X → Y)
    (he : IsEmbedding e) (f : X → E) (hf : @Continuous X E _ scottTopologicalSpace f) (x₀ : X) :
    scottExtend e f (e x₀) = f x₀ := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro d ⟨V, hVo, hex₀V, rfl⟩
    exact sInf_le ⟨x₀, hex₀V, rfl⟩
  · rw [← hE.sSup_wayBelow (f x₀)]
    refine sSup_le fun a ha => ?_
    have hWopen : @IsOpen E scottTopologicalSpace {z : E | a ≪ z} :=
      isOpen_iff_scottOpen.mpr (scottOpen_wayBelow a)
    have hpre : IsOpen (f ⁻¹' {z : E | a ≪ z}) := continuous_def.mp hf _ hWopen
    rw [he.isInducing.isOpen_iff] at hpre
    obtain ⟨V, hVo, hVeq⟩ := hpre
    have hx₀V : x₀ ∈ e ⁻¹' V := by rw [hVeq]; exact ha
    refine le_trans ?_ (le_sSup ⟨V, hVo, hx₀V, rfl⟩)
    refine le_sInf ?_
    rintro w ⟨x, hxV, rfl⟩
    have hxW : x ∈ f ⁻¹' {z : E | a ≪ z} := by rw [← hVeq]; exact hxV
    exact (hxW : a ≪ f x).le
end Scott1972.ContinuousLattice

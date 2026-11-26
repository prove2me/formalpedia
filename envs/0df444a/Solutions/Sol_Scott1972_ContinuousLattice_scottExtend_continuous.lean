-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottExtend_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:33:03.663706+00:00
-- url     : https://prove2.me/submissions/1aa2e435-65d7-4302-b299-143e4efcfc93

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Theorems.Thm_Scott1972_ContinuousLattice_scottExtend_aux_nonempty
import Theorems.Thm_Scott1972_ContinuousLattice_scottExtend_aux_directed
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_trans_le
import Theorems.Thm_Scott1972_ContinuousLattice_exists_wayBelow_subset
import Theorems.Thm_Scott1972_ContinuousLattice_isOpen_iff_scottOpen
import Theorems.Thm_Scott1972_ContinuousLattice_wayBelow_sSup_iff


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]
namespace Scott1972.ContinuousLattice
theorem _root_.solution (hE : IsContinuousLattice E) (e : X → Y) (f : X → E) :
    @Continuous Y E _ scottTopologicalSpace (scottExtend e f) := by
  letI : TopologicalSpace E := scottTopologicalSpace
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff_scottOpen] at hU
  rw [isOpen_iff_forall_mem_open]
  intro y₀ hy₀
  have hgy₀U : scottExtend e f y₀ ∈ U := hy₀
  obtain ⟨a, haz, hasub⟩ := exists_wayBelow_subset hE hU hgy₀U
  obtain ⟨d, hd, had⟩ := (wayBelow_sSup_iff (scottExtend_aux_nonempty e f y₀)
    (scottExtend_aux_directed e f y₀)).1 haz
  obtain ⟨V, hVo, hy₀V, rfl⟩ := hd
  refine ⟨V, ?_, hVo, hy₀V⟩
  intro y' hy'V
  show scottExtend e f y' ∈ U
  refine hasub ?_
  show a ≪ scottExtend e f y'
  exact had.trans_le (le_sSup ⟨V, hVo, hy'V, rfl⟩)
end Scott1972.ContinuousLattice

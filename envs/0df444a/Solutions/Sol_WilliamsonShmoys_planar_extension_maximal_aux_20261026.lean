-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_maximal_aux_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:10:27.015837+00:00
-- url     : https://prove2.me/submissions/65cdb05c-cb04-4b3a-935e-c91123bbe2e6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_nat_max_on_nonempty_predicate
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_lt_of_subset_ne

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      Set.Subset H.edgeSet K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        Set.Subset K.edgeSet L.edgeSet →
        HasPlanarDrawingOn L →
        K.edgeSet = L.edgeSet := by
  classical
  let P : SimpleGraph V → Prop :=
    fun K => H.edgeSet ⊆ K.edgeSet ∧ HasPlanarDrawingOn K
  obtain ⟨K, hK, hmax⟩ :=
    WilliamsonShmoys.exists_nat_max_on_nonempty_predicate
      P (fun G => Set.ncard G.edgeSet) ⟨H, subset_rfl, hH⟩
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hL
  by_contra hneq
  have hlt := WilliamsonShmoys.edgeSet_ncard_lt_of_subset_ne K L hKL hneq
  have hle := hmax L ⟨hK.1.trans hKL, hL⟩
  omega
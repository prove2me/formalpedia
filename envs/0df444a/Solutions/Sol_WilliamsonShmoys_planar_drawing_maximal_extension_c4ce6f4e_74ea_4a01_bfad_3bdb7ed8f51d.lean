-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_c4ce6f4e_74ea_4a01_bfad_3bdb7ed8f51d
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:11:14.491984+00:00
-- url     : https://prove2.me/submissions/2b0caf01-245c-4691-9c8b-4aa92af45d7a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

set_option autoImplicit false

open Classical

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ H : SimpleGraph V,
      W ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K ≤ H) ∧
      W.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  let p : SimpleGraph V → Prop :=
    fun G => W ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hp : ∃ G : SimpleGraph V, p G := ⟨W, le_rfl, hW⟩
  obtain ⟨H, hDec, hExt⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 hp
  letI := hDec
  refine ⟨H, hExt.1.1, hExt.1.2, ?_, ?_⟩
  · intro K hK hHK
    have hPK : p K := ⟨hExt.1.1.trans hHK, hK⟩
    exact le_of_eq ((SimpleGraph.IsExtremal.le_iff_eq hExt hPK).mp hHK).symm
  · exact Set.ncard_mono (SimpleGraph.edgeSet_subset_edgeSet.mpr hExt.1.1)
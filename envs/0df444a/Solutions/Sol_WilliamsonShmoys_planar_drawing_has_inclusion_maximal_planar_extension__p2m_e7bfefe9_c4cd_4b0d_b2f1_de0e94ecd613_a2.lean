-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_inclusion_maximal_planar_extension__p2m_e7bfefe9_c4cd_4b0d_b2f1_de0e94ecd613_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:16:23.758093+00:00
-- url     : https://prove2.me/submissions/63f59d92-cf89-4478-a7af-54b4fdc7573c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V,
      M.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet := by
  classical
  let p : SimpleGraph V → Prop := fun G => M ≤ G ∧ HasPlanarDrawingOn G
  have hex : ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj, G.IsExtremal p := by
    apply (SimpleGraph.exists_isExtremal_iff_exists (V := V) p).2
    exact ⟨M, le_rfl, hM⟩
  obtain ⟨H, dH, hExt⟩ := hex
  letI : DecidableRel H.Adj := dH
  refine ⟨H, SimpleGraph.edgeSet_subset_edgeSet.mpr hExt.1.1, hExt.1.2, ?_⟩
  intro K hHK hK
  have hMK : M ≤ K := le_trans hExt.1.1 (SimpleGraph.edgeSet_subset_edgeSet.mp hHK)
  have hKp : p K := ⟨hMK, hK⟩
  have hEq : H = K :=
    (SimpleGraph.IsExtremal.le_iff_eq hExt hKp).mp
      (SimpleGraph.edgeSet_subset_edgeSet.mp hHK)
  rw [hEq]
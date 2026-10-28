-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_edge_maximal_supergraph_repair_1c3af418_60f6_43cb_bce2_5b8b37d68734
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T07:24:17.588107+00:00
-- url     : https://prove2.me/submissions/2940a292-7107-4aaf-93cf-3784ec38dff4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet ⊆ N.edgeSet ∧
      (∀ P : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn P →
        N.edgeSet ⊆ P.edgeSet → P.edgeSet = N.edgeSet) := by
  classical
  obtain ⟨Qx9, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => M ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hM⟩⟩
  obtain ⟨hPQ, hQ⟩ : M ≤ Qx9 ∧ WilliamsonShmoys.HasPlanarDrawingOn Qx9 := (Finset.mem_filter.mp hQm).2
  have key : ∀ Rx9 : SimpleGraph V, Qx9 ≤ Rx9 → WilliamsonShmoys.HasPlanarDrawingOn Rx9 → Rx9 = Qx9 := by
    intro Rx9 hQR hR
    by_contra hne
    have hlt : Qx9 < Rx9 := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax Rx9 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  refine ⟨Qx9, ?_⟩
  repeat' apply And.intro
  all_goals first
    | exact hQ
    | exact hPQ
    | exact SimpleGraph.edgeSet_subset_edgeSet.mpr hPQ
    | exact fun _ _ h => hPQ h
    | (apply SimpleGraph.Connected.mono hPQ; assumption)
    | exact Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.mpr hPQ) (Set.toFinite _)
    | (intro Rx9 ha hb; have e := key Rx9 (by first | exact ha | exact SimpleGraph.edgeSet_subset_edgeSet.mp ha | exact fun _ _ h => ha h | exact ha.le | exact SimpleGraph.edgeSet_subset_edgeSet.mp ha.subset) hb; subst e; first | rfl | exact le_rfl | exact subset_rfl | exact fun _ _ h => h)
    | (intro Rx9 hb ha; have e := key Rx9 (by first | exact ha | exact SimpleGraph.edgeSet_subset_edgeSet.mp ha | exact fun _ _ h => ha h | exact ha.le | exact SimpleGraph.edgeSet_subset_edgeSet.mp ha.subset) hb; subst e; first | rfl | exact le_rfl | exact subset_rfl | exact fun _ _ h => h)
    | (intro Rx9 ha hb hc; have e := key Rx9 (by first | exact ha | exact SimpleGraph.edgeSet_subset_edgeSet.mp ha | exact fun _ _ h => ha h | exact ha.le | exact SimpleGraph.edgeSet_subset_edgeSet.mp ha.subset) hc; subst e; exact absurd rfl hb)
    | (intro Rx9 ha hb; have e := key Rx9 (SimpleGraph.edgeSet_subset_edgeSet.mp ha.subset) hb; subst e; exact (ha.ne rfl).elim)
    | (intro Rx9 ha hb; have e := key Rx9 (SimpleGraph.edgeSet_subset_edgeSet.mp ha.subset) hb; subst e; exact (ha.ne rfl))
    | (intro Rx9 ha hb; have hm := hmax Rx9 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hb⟩); simp only [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]; exact hm)

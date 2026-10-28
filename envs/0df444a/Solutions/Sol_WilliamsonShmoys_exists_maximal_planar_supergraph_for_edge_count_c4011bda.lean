-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_count_c4011bda
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:53:38.922669+00:00
-- url     : https://prove2.me/submissions/f4c80d82-bb1f-4db0-bd8f-86b877f84553

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V,
      L ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        ∀ S : SimpleGraph V,
          WilliamsonShmoys.HasPlanarDrawingOn S → T ≤ S → S ≤ T := by
  classical
  obtain ⟨Qx9, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => L ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hL⟩⟩
  obtain ⟨hPQ, hQ⟩ : L ≤ Qx9 ∧ WilliamsonShmoys.HasPlanarDrawingOn Qx9 := (Finset.mem_filter.mp hQm).2
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

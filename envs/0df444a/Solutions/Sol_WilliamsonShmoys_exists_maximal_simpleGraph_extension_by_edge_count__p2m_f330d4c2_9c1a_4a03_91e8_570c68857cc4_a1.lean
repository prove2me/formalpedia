-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_simpleGraph_extension_by_edge_count__p2m_f330d4c2_9c1a_4a03_91e8_570c68857cc4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:24:52.112947+00:00
-- url     : https://prove2.me/submissions/739e1b54-c796-44a5-8dc7-78949983cf90

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

noncomputable section

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧ P H ∧
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       G.edgeFinset.card ≤ H.edgeFinset.card) ∧
      (∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) → P K →
          (letI : DecidableRel H.Adj := Classical.decRel H.Adj
           letI : DecidableRel K.Adj := Classical.decRel K.Adj
           K.edgeFinset.card ≤ H.edgeFinset.card)) := by
  classical
  letI : Fintype (SimpleGraph V) := inferInstance
  let candidates : Finset (SimpleGraph V) := Finset.univ.filter fun X =>
    (∀ ⦃u v : V⦄, G.Adj u v → X.Adj u v) ∧ P X
  have hGmem : G ∈ candidates := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, ⟨by intro u v huv; exact huv, hG⟩⟩
  have hnonempty : candidates.Nonempty := ⟨G, hGmem⟩
  obtain ⟨H, hHmem, hHmax⟩ :=
    Finset.exists_max_image candidates (fun X => X.edgeFinset.card) hnonempty
  have hHG : ∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v :=
    (Finset.mem_filter.mp hHmem).2.1
  have hHP : P H := (Finset.mem_filter.mp hHmem).2.2
  refine ⟨H, hHG, hHP, hHmax G hGmem, ?_⟩
  intro K hHK hK
  apply hHmax K
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ K, ?_⟩
  constructor
  · intro u v huv
    exact hHK (hHG huv)
  · exact hK

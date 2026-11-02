-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_extension__p2m_18964b7c_c181_43c8_b19b_00116e3fbbcb_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:12:12.547551+00:00
-- url     : https://prove2.me/submissions/217f7c65-2e57-42a6-94db-951e1c83deb9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      H.edgeFinset ⊆ K.edgeFinset ∧
      HasPlanarDrawingOn K ∧
      (∀ (L : SimpleGraph V) [DecidableRel L.Adj],
        (∀ {u v}, K.Adj u v → L.Adj u v) →
        HasPlanarDrawingOn L →
        ∀ {u v}, L.Adj u v → K.Adj u v) := by
  classical
  let P : SimpleGraph V → Prop := fun G => H ≤ G ∧ HasPlanarDrawingOn G
  have hP : ∃ G : SimpleGraph V, P G := ⟨H, le_rfl, hH⟩
  obtain ⟨K, dK, hK⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists P).2 hP
  letI : DecidableRel K.Adj := dK
  refine ⟨K, dK, SimpleGraph.edgeFinset_subset_edgeFinset.2 hK.1.1,
    hK.1.2, ?_⟩
  intro L instL hKL hL
  letI : DecidableRel L.Adj := instL
  intro u v hLuv
  have hKL' : K ≤ L := fun _ _ huv => hKL huv
  have hPL : P L := ⟨hK.1.1.trans hKL', hL⟩
  have hcard : L.edgeFinset.card ≤ K.edgeFinset.card := hK.2 hPL
  have hsub : K.edgeFinset ⊆ L.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.2 hKL'
  have heq : K.edgeFinset = L.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub hcard
  have hgraphs : K = L := SimpleGraph.edgeFinset_inj.mp heq
  simpa [hgraphs] using hLuv
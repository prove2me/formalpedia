-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_303ddd52_95e9_4125_a752_478be76ea7a5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:42:03.302279+00:00
-- url     : https://prove2.me/submissions/b3a7d624-ad1f-469a-bba3-2d7dad631d26

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hU : HasPlanarDrawingOn U)
    (hconn : U.Connected) :
    ∃ T : SimpleGraph V, U ≤ T ∧ HasPlanarDrawingOn T ∧ T.Connected ∧
      ∀ S : SimpleGraph V, T ≤ S → HasPlanarDrawingOn S → S = T := by
  classical
  let C : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G : SimpleGraph V =>
      U ≤ G ∧ HasPlanarDrawingOn G)
  have hC : C.Nonempty := by
    refine ⟨U, ?_⟩
    change U ∈ Finset.univ.filter (fun G : SimpleGraph V =>
      U ≤ G ∧ HasPlanarDrawingOn G)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_rfl, hU⟩
  obtain ⟨T, hTm, hmax⟩ :=
    Finset.exists_max_image C (fun G => G.edgeFinset.card) hC
  have hTm' : T ∈ Finset.univ.filter (fun G : SimpleGraph V =>
      U ≤ G ∧ HasPlanarDrawingOn G) := by
    simpa [C] using hTm
  have hmem := Finset.mem_filter.mp hTm'
  have hTU : U ≤ T := hmem.2.1
  have hTd : HasPlanarDrawingOn T := hmem.2.2
  refine ⟨T, hTU, hTd, hconn.mono hTU, ?_⟩
  intro S hTS hSd
  by_contra hne
  have hlt : T < S := lt_of_le_of_ne hTS (Ne.symm hne)
  have hss : T.edgeFinset ⊂ S.edgeFinset :=
    SimpleGraph.edgeFinset_strict_mono hlt
  have hcard : T.edgeFinset.card < S.edgeFinset.card :=
    Finset.card_lt_card hss
  have hSm : S ∈ C := by
    change S ∈ Finset.univ.filter (fun G : SimpleGraph V =>
      U ≤ G ∧ HasPlanarDrawingOn G)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hTU.trans hTS, hSd⟩
  exact (not_lt_of_ge (hmax S hSm)) hcard
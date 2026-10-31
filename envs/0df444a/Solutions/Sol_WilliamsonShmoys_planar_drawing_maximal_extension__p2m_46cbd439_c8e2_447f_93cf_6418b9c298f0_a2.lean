-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_46cbd439_c8e2_447f_93cf_6418b9c298f0_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:49:35.341282+00:00
-- url     : https://prove2.me/submissions/7ada15ea-6aed-4a03-bca5-a44890488c14

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      (∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) := by
  classical
  let good : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => M ≤ G ∧ HasPlanarDrawingOn G)
  have hgood : good.Nonempty := by
    refine ⟨M, ?_⟩
    simp [good, hM]
  obtain ⟨N, hNmem, hNmax⟩ :=
    Finset.exists_max_image good (fun G : SimpleGraph V => G.edgeFinset.card) hgood
  have hNgood : M ≤ N ∧ HasPlanarDrawingOn N := by
    simpa [good] using hNmem
  rcases hNgood with ⟨hMN, hPlanarN⟩
  refine ⟨N, hMN, hPlanarN, ?_⟩
  intro K hNK hPlanarK
  have hKmem : K ∈ good := by
    simp [good, hMN.trans hNK, hPlanarK]
  have hmax : K.edgeFinset.card ≤ N.edgeFinset.card := hNmax K hKmem
  have hsubset : N.edgeFinset ⊆ K.edgeFinset :=
    SimpleGraph.edgeFinset_mono hNK
  have heq : N.edgeFinset = K.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsubset hmax
  have hgraph : N = K := SimpleGraph.edgeFinset_inj.mp heq
  simpa [hgraph]
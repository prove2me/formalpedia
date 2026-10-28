-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:24:43.788486+00:00
-- url     : https://prove2.me/submissions/a0b79faf-9a78-427b-a3ed-e1c1e20f277e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      Q ≤ R ∧ WilliamsonShmoys.HasPlanarDrawingOn R ∧
        ∀ S : SimpleGraph V, R ≤ S →
          WilliamsonShmoys.HasPlanarDrawingOn S → S = R := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => Q ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hQmem : Q ∈ candidates := by
    simp [candidates, hQdraw]
  obtain ⟨R, hRmem, hRmax⟩ :=
    candidates.exists_max_image (fun G : SimpleGraph V => G.edgeFinset.card)
      ⟨Q, hQmem⟩
  have hRQ : Q ≤ R := by
    simpa [candidates] using (Finset.mem_filter.mp hRmem).2.1
  have hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R := by
    simpa [candidates] using (Finset.mem_filter.mp hRmem).2.2
  refine ⟨R, hRQ, hRdraw, ?_⟩
  intro S hRS hSdraw
  have hSmem : S ∈ candidates := by
    simp [candidates, le_trans hRQ hRS, hSdraw]
  have hmax : S.edgeFinset.card ≤ R.edgeFinset.card := hRmax S hSmem
  have hsub : R.edgeFinset ⊆ S.edgeFinset := SimpleGraph.edgeFinset_mono hRS
  have hcards : R.edgeFinset.card = S.edgeFinset.card :=
    Nat.le_antisymm (Finset.card_le_card hsub) hmax
  have hedge : R.edgeFinset = S.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub (Nat.le_of_eq hcards.symm)
  exact SimpleGraph.edgeFinset_inj.mp hedge.symm
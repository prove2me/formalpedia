-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_augmentation__p2m_1c06af72_8ad5_473e_9376_40ba591256d7_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:28:20.484761+00:00
-- url     : https://prove2.me/submissions/e2d0632f-0617-46b8-9041-8a90819e54bf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : HasPlanarDrawingOn G) :
    (letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj;
      ∃ H : SimpleGraph V,
        G ≤ H ∧ HasPlanarDrawingOn H ∧
          (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) ∧
          G.edgeFinset.card ≤ H.edgeFinset.card) := by
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
  let candidates : Set (SimpleGraph V) :=
    {K | G ≤ K ∧ HasPlanarDrawingOn K}
  have hfinite : candidates.Finite := by
    apply Set.finite_univ.subset
    intro K hK
    exact Set.mem_univ K
  have hnonempty : candidates.Nonempty := ⟨G, le_rfl, hdrawing⟩
  obtain ⟨H, hH, hmax⟩ :=
    Set.exists_max_image candidates (fun K => K.edgeFinset.card) hfinite hnonempty
  refine ⟨H, hH.1, hH.2, ?_, ?_⟩
  · intro K hHK hKdraw
    have hKcandidate : K ∈ candidates := ⟨le_trans hH.1 hHK, hKdraw⟩
    have hcard_le : H.edgeFinset.card ≤ K.edgeFinset.card :=
      Finset.card_le_card (SimpleGraph.edgeFinset_mono hHK)
    have hmaxK : K.edgeFinset.card ≤ H.edgeFinset.card := hmax K hKcandidate
    have hcard_eq : H.edgeFinset.card = K.edgeFinset.card :=
      Nat.le_antisymm hcard_le hmaxK
    have hedge_subset : H.edgeFinset ⊆ K.edgeFinset :=
      SimpleGraph.edgeFinset_mono hHK
    have hedge_eq : H.edgeFinset = K.edgeFinset :=
      Finset.eq_of_subset_of_card_le hedge_subset (Nat.le_of_eq hcard_eq.symm)
    symm
    apply le_antisymm hHK
    intro u v huv
    have hmem : (s(u, v) : Sym2 V) ∈ K.edgeFinset := by
      simpa using huv
    have hmem' : (s(u, v) : Sym2 V) ∈ H.edgeFinset := by
      rw [hedge_eq]
      exact hmem
    simpa using hmem'
  · exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hH.1)
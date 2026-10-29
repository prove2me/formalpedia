-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_337d3ec9_bc9c_4a02_9472_77e31d84e6a7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T00:13:25.272658+00:00
-- url     : https://prove2.me/submissions/32d0930a-c796-452a-aed4-e1ae409d9ee0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      (∀ x y, T.Adj x y → U.Adj x y) ∧
      HasPlanarDrawingOn U ∧
      ∀ W : SimpleGraph V,
        (∀ x y, U.Adj x y → W.Adj x y) →
        HasPlanarDrawingOn W → W = U := by
  classical
  obtain ⟨U, hdec, hmax⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists
      (p := fun G : SimpleGraph V => T ≤ G ∧ HasPlanarDrawingOn G)).2
      ⟨T, le_rfl, hT⟩
  letI : DecidableRel U.Adj := hdec
  rcases hmax with ⟨hprop, hmax⟩
  refine ⟨U, ?_, hprop.2, ?_⟩
  · intro x y hxy
    exact hprop.1 hxy
  · intro W hUW hW
    have hTW : T ≤ W := fun x y hxy => hUW x y (hprop.1 hxy)
    have hmaxW : W.edgeFinset.card ≤ U.edgeFinset.card :=
      hmax ⟨hTW, hW⟩
    have hsub : U.edgeFinset ⊆ W.edgeFinset :=
      SimpleGraph.edgeFinset_subset_edgeFinset.mpr hUW
    have heq : U.edgeFinset = W.edgeFinset :=
      Finset.eq_of_subset_of_card_le hsub hmaxW
    exact SimpleGraph.edgeFinset_inj.mp heq.symm
-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_completion__p2m_0d4fbf3e_ba5d_4358_a028_c1fcc85193dd_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:53:47.312074+00:00
-- url     : https://prove2.me/submissions/82abf113-40a3-45c1-a85c-341bbfce0ac6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

namespace S216WS

lemma exists_maximal {V : Type} [Fintype V] (W : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P W) : ∃ H : SimpleGraph V, W ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  obtain ⟨H, ⟨hWH, hPH⟩, hmax⟩ := Set.Finite.exists_maximal
    (s := {G : SimpleGraph V | W ≤ G ∧ P G}) (Set.toFinite _) ⟨W, le_rfl, hP⟩
  exact ⟨H, hWH, hPH, fun K hHK hPK => le_antisymm (hmax ⟨le_trans hWH hHK, hPK⟩ hHK) hHK⟩

end S216WS


open WilliamsonShmoys in
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      (∀ G : SimpleGraph V,
        H.edgeSet ⊆ G.edgeSet → HasPlanarDrawingOn G → G.edgeSet = H.edgeSet) := by
  obtain ⟨H,h1,h2,h3⟩ := S216WS.exists_maximal K _ hK
  exact ⟨H,SimpleGraph.edgeSet_mono h1,h2,fun G a b => by rw [h3 G (SimpleGraph.edgeSet_subset_edgeSet.mp a) b]⟩

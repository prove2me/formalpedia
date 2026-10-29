-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_ef0860d4_4cfe_4ed1_9f37_9a24872db6ea_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:10:30.020509+00:00
-- url     : https://prove2.me/submissions/2d5ff77e-356a-400a-bc4c-616562d85bda

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      T ≤ U ∧
      ∀ W : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn W → U ≤ W → W ≤ U := by
  have hF : Finite (SimpleGraph V) :=
    Finite.of_injective (fun G : SimpleGraph V => G.Adj) (fun _ _ h => SimpleGraph.ext h)
  obtain ⟨U, hU⟩ := (Set.toFinite {U : SimpleGraph V | T ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U}).exists_maximal ⟨T, le_rfl, hT⟩
  exact ⟨U, hU.1.2, hU.1.1, fun W hW hUW => hU.2 ⟨hU.1.1.trans hUW, hW⟩ hUW⟩

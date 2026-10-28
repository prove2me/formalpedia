-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_extension_by_edge_max_e86e41b9
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:13:46.939665+00:00
-- url     : https://prove2.me/submissions/27000f9b-85bb-47de-aa9d-7963f832c3af

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Order.Preorder.Finite

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    exists L : SimpleGraph V,
      K <= L /\ HasPlanarDrawingOn L /\
        (forall M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M = L) := by
  classical
  let S : Set (SimpleGraph V) := {L | K <= L /\ HasPlanarDrawingOn L}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := Exists.intro K (And.intro le_rfl hK)
  have hExists := hSfinite.exists_maximal hSnonempty
  cases hExists with
  | intro L hLmax =>
    refine Exists.intro L ?_
    refine And.intro hLmax.1.1 ?_
    refine And.intro hLmax.1.2 ?_
    intro M hLM hM
    have hMmem : M ∈ S := And.intro (hLmax.1.1.trans hLM) hM
    exact le_antisymm (hLmax.2 hMmem hLM) hLM
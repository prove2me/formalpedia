-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_connected__p2m_24055289_8edd_427c_8cf4_b86f3a2eaef9_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:33:38.749365+00:00
-- url     : https://prove2.me/submissions/8d8fd96b-b461-4d7d-b980-628257b1b6af

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (H : SimpleGraph V),
        HasPlanarDrawingOn H →
        (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) →
        H.Connected) := by
  intro hAll
  letI : Fintype Empty := inferInstance
  letI : LinearOrder Empty := inferInstance
  let H : SimpleGraph Empty := ⊥
  have hDrawing : HasPlanarDrawingOn H := by
    refine ⟨(fun x : Empty => nomatch x), (fun x : Empty => nomatch x), ?_, ?_, ?_⟩
    · intro x
      cases x
    · intro u
      cases u
    · intro u
      cases u
  have hMaximal :
      ∀ K : SimpleGraph Empty, H ≤ K → HasPlanarDrawingOn K → K ≤ H := by
    intro K hHK hK
    intro u v huv
    cases u
  have hConn : H.Connected := hAll H hDrawing hMaximal
  rcases hConn.nonempty with ⟨v⟩
  cases v
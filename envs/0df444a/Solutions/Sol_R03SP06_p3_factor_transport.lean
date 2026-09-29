-- Prove2me | solution 1 for R03SP06.p3_factor_transport
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:04:04.353395+00:00
-- url     : https://prove2.me/submissions/a0374f58-d753-4d3b-875d-08a9aa627900

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP06

open CubicP3Partition


end R03SP06

open R03SP06
open CubicP3Partition
theorem solution
    {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (e : V ≃ W)
    (hadj : ∀ x y, H.Adj x y → G.Adj (e x) (e y))
    (hfactor : Nonempty (P3Factor H)) :
    Nonempty (P3Factor G) := by
  obtain ⟨p⟩ := hfactor
  let place : (Fin p.blockCount × Fin 3) ≃ W := p.place.trans e
  refine ⟨{
    blockCount := p.blockCount
    place := place
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    simpa [place, Equiv.trans_apply] using hadj
      (p.place (i, (0 : Fin 3))) (p.place (i, 1)) (p.edge01 i)
  · intro i
    simpa [place, Equiv.trans_apply] using hadj
      (p.place (i, (1 : Fin 3))) (p.place (i, 2)) (p.edge12 i)


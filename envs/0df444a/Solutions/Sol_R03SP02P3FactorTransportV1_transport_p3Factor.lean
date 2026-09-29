-- Prove2me | solution 1 for R03SP02P3FactorTransportV1.transport_p3Factor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:55:08.399641+00:00
-- url     : https://prove2.me/submissions/686097df-320b-4429-8a01-fb7e1b6cc81e

import Definitions.Def_cubic_p3_partition_models

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace R03SP02P3FactorTransportV1

open CubicP3Partition

noncomputable section


end
end R03SP02P3FactorTransportV1

open R03SP02P3FactorTransportV1
open CubicP3Partition
theorem solution
    {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : V ≃ W)
    (hAdj : ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y))
    (hFactor : Nonempty (P3Factor G)) :
    Nonempty (P3Factor H) := by
  obtain ⟨f⟩ := hFactor
  let p : (Fin f.blockCount × Fin 3) ≃ W := Equiv.trans f.place e
  refine ⟨{ blockCount := f.blockCount, place := p, edge01 := ?_, edge12 := ?_ }⟩
  · intro i
    apply (hAdj (f.place (i, 0)) (f.place (i, 1))).mp
    exact f.edge01 i
  · intro i
    apply (hAdj (f.place (i, 1)) (f.place (i, 2))).mp
    exact f.edge12 i


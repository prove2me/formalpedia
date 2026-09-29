-- Prove2me | solution 1 for R03SP02P3FactorAssignmentTransportV1.p3Factor_of_bijective_assignment
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:54:55.221473+00:00
-- url     : https://prove2.me/submissions/09f51eb5-6cff-4d28-a213-68218d2a4a82

import Definitions.Def_cubic_p3_partition_models

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace R03SP02P3FactorAssignmentTransportV1

open CubicP3Partition

noncomputable section


end
end R03SP02P3FactorAssignmentTransportV1

open R03SP02P3FactorAssignmentTransportV1
open CubicP3Partition
theorem solution
    {G : SimpleGraph (Fin 12)}
    (place : Fin 4 × Fin 3 → Fin 12)
    (hbij : Function.Bijective place)
    (hedge01 : ∀ i : Fin 4, G.Adj (place (i, 0)) (place (i, 1)))
    (hedge12 : ∀ i : Fin 4, G.Adj (place (i, 1)) (place (i, 2))) :
    Nonempty (P3Factor G) := by
  let e : (Fin 4 × Fin 3) ≃ Fin 12 := Equiv.ofBijective place hbij
  exact ⟨{
    blockCount := 4
    place := e
    edge01 := hedge01
    edge12 := hedge12
  }⟩


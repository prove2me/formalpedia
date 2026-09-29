-- Prove2me | solution 1 for R03SP02P3FactorCardinalityV1.p3Factor_order_divisible_by_three
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:54:58.307258+00:00
-- url     : https://prove2.me/submissions/f9c0839a-4f31-43bd-8119-638e6de6edd1

import Definitions.Def_cubic_p3_partition_models

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace R03SP02P3FactorCardinalityV1

open CubicP3Partition

noncomputable section

theorem p3Factor_cardinality
    {V : Type} [Fintype V]
    {G : SimpleGraph V} (f : P3Factor G) :
    Fintype.card V = f.blockCount * 3 := by
  have hc : Fintype.card (Fin f.blockCount × Fin 3) = Fintype.card V :=
    Fintype.card_congr f.place
  simpa using hc.symm


end
end R03SP02P3FactorCardinalityV1

open R03SP02P3FactorCardinalityV1
open CubicP3Partition
theorem solution
    {V : Type} [Fintype V]
    {G : SimpleGraph V} (f : P3Factor G) :
    3 ∣ Fintype.card V := by
  refine ⟨f.blockCount, ?_⟩
  simpa [Nat.mul_comm] using p3Factor_cardinality f


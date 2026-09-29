-- Prove2me | solution 1 for R03SP02P3FactorCardinalityV1.p3Factor_blockCount_eq_four_of_order_twelve
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:55:06.333766+00:00
-- url     : https://prove2.me/submissions/412bc826-0d49-46dd-a9da-1f28b2f6c79c

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

theorem p3Factor_order_divisible_by_three
    {V : Type} [Fintype V]
    {G : SimpleGraph V} (f : P3Factor G) :
    3 ∣ Fintype.card V := by
  refine ⟨f.blockCount, ?_⟩
  simpa [Nat.mul_comm] using p3Factor_cardinality f


end
end R03SP02P3FactorCardinalityV1

open R03SP02P3FactorCardinalityV1
open CubicP3Partition
theorem solution
    {V : Type} [Fintype V]
    {G : SimpleGraph V} (f : P3Factor G)
    (hcard : Fintype.card V = 12) :
    f.blockCount = 4 := by
  have hc := p3Factor_cardinality f
  rw [hcard] at hc
  omega


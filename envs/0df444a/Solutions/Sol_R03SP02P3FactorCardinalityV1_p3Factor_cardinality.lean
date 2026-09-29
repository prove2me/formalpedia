-- Prove2me | solution 1 for R03SP02P3FactorCardinalityV1.p3Factor_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:54:56.747022+00:00
-- url     : https://prove2.me/submissions/b14b1cdf-0a4d-479a-8909-32d801cd505f

import Definitions.Def_cubic_p3_partition_models

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace R03SP02P3FactorCardinalityV1

open CubicP3Partition

noncomputable section


end
end R03SP02P3FactorCardinalityV1

open R03SP02P3FactorCardinalityV1
open CubicP3Partition
theorem solution
    {V : Type} [Fintype V]
    {G : SimpleGraph V} (f : P3Factor G) :
    Fintype.card V = f.blockCount * 3 := by
  have hc : Fintype.card (Fin f.blockCount × Fin 3) = Fintype.card V :=
    Fintype.card_congr f.place
  simpa using hc.symm


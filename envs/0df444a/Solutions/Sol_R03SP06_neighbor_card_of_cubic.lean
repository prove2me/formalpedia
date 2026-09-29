-- Prove2me | solution 1 for R03SP06.neighbor_card_of_cubic
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:47:56.437619+00:00
-- url     : https://prove2.me/submissions/bef4741c-5fd6-459b-b8fc-1865e7fb50c2

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP06

open CubicP3Partition

variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def externalNeighborsExact (G : SimpleGraph V) (S : Finset V) (v : V) : Finset V := by
  classical
  exact (G.neighborFinset v).filter (fun w => w ∉ S)


end R03SP06

open R03SP06
open CubicP3Partition
variable {V : Type} [Fintype V] [DecidableEq V]
theorem solution
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : Cubic G) : ∀ v : V, (G.neighborFinset v).card = 3 := by
  intro v
  have hcard : (G.neighborFinset v).card = Nat.card {w : V // G.Adj v w} := by
    change (G.neighborFinset v).card = Nat.card (G.neighborSet v)
    rw [Nat.card_coe_set_eq]
    symm
    simpa [SimpleGraph.neighborFinset] using
      (Set.ncard_eq_toFinset_card' (G.neighborSet v))
  exact (hcard.trans (hC v))


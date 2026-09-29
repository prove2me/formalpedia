-- Prove2me | solution 1 for R03SP03PetersenMatchingBridge.project_perfectMatching_of_subgraph
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:03:47.731187+00:00
-- url     : https://prove2.me/submissions/2a554b97-6de0-4ec1-9ae0-0a00caff1cb0

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP03PetersenMatchingBridge

open CubicP3Partition

universe u

variable {V : Type u} [Fintype V]


end R03SP03PetersenMatchingBridge

open R03SP03PetersenMatchingBridge
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
theorem solution
    {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsPerfectMatching) :
    CubicP3Partition.PerfectMatching G M.spanningCoe := by
  refine ⟨M.spanningCoe_le, ?_⟩
  intro v
  letI : Fintype {w : V // M.Adj v w} := Fintype.ofFinite _
  change Nat.card {w : V // M.Adj v w} = 1
  rw [Nat.card_eq_fintype_card]
  apply Fintype.card_eq_one_iff.mpr
  obtain ⟨w, hw, huw⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM) v
  refine ⟨⟨w, hw⟩, ?_⟩
  intro z
  exact Subtype.ext (huw z.val z.property)


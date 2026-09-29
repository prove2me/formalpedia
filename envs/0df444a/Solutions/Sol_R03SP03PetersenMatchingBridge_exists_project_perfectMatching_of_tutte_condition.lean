-- Prove2me | solution 1 for R03SP03PetersenMatchingBridge.exists_project_perfectMatching_of_tutte_condition
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:03:46.038186+00:00
-- url     : https://prove2.me/submissions/f3dcb1fe-1855-44fc-a7c8-9d509627b1f5

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP03PetersenMatchingBridge

open CubicP3Partition

universe u

variable {V : Type u} [Fintype V]

/-- Convert Mathlib's spanning-subgraph formulation of a perfect matching to
 the project-level graph formulation. -/
theorem project_perfectMatching_of_subgraph
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


end R03SP03PetersenMatchingBridge

open R03SP03PetersenMatchingBridge
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
theorem solution
    {G : SimpleGraph V}
    (hNoViolator : ∀ u : Set V, ¬ G.IsTutteViolator u) :
    ∃ M : SimpleGraph V, CubicP3Partition.PerfectMatching G M := by
  obtain ⟨M, hM⟩ := (SimpleGraph.tutte (G := G)).mpr hNoViolator
  exact ⟨M.spanningCoe, project_perfectMatching_of_subgraph hM⟩


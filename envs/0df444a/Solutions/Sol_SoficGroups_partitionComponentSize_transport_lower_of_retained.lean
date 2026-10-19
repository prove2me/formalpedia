-- Prove2me | solution 1 for SoficGroups.partitionComponentSize_transport_lower_of_retained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/cd63b169-b890-45d0-9c25-df21088f1a02

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_maximumOverlapPart_mem
import Theorems.Thm_SoficGroups_partitionComponentSize_transport_lower_of_overlap
import Theorems.Thm_SoficGroups_maximumOverlapPart_overlap_of_not_mem_insufficient

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : Type u} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (C : Finset V) (hC : C ∈ Q.parts)
    (eta : ℝ)
    (hretained : C.map T.toEmbedding ∉
      insufficientOverlapComponents
        (transportedUnivFinpartition Q T) Q eta)
    (x : V) (hx : x ∈ C)
    (hTx : T x ∈ maximumOverlapPart Q (C.map T.toEmbedding)) :
    (1 - eta) * (partitionComponentSize Q x : ℝ) ≤
      (partitionComponentSize Q (T x) : ℝ) := by
  have htransport : C.map T.toEmbedding ∈
      (transportedUnivFinpartition Q T).parts := by
    rw [transportedUnivFinpartition_parts]
    exact Finset.mem_image_of_mem
      (fun C : Finset V => C.map T.toEmbedding) hC
  have hsize := maximumOverlapPart_overlap_of_not_mem_insufficient
    (transportedUnivFinpartition Q T) Q eta
    (C.map T.toEmbedding) htransport hretained
  have hsize' :
      (1 - eta) * (C.card : ℝ) ≤
        (((C.map T.toEmbedding) ∩
          maximumOverlapPart Q (C.map T.toEmbedding)).card : ℝ) := by
    simpa using hsize
  have htarget := maximumOverlapPart_mem Q
    (C.map T.toEmbedding)
    ((Finset.map_nonempty).2 (Q.nonempty_of_mem_parts hC))
    (Finset.subset_univ _)
  exact partitionComponentSize_transport_lower_of_overlap Q T C
    (maximumOverlapPart Q (C.map T.toEmbedding)) hC htarget
    eta hsize' x hx hTx
end SoficGroups

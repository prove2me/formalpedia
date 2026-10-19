-- Prove2me | solution 1 for SoficGroups.partitionComponentSize_transport_lower_of_overlap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/9c23e80b-02d3-4e3b-8956-bc5511723513

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_partitionComponentSize_eq_card_of_mem

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (T : Equiv.Perm V)
    (C D : Finset V) (hC : C ∈ Q.parts) (hD : D ∈ Q.parts)
    (eta : ℝ)
    (hoverlap :
      (1 - eta) * (C.card : ℝ) ≤
        (((C.map T.toEmbedding) ∩ D).card : ℝ))
    (x : V) (hx : x ∈ C) (hTx : T x ∈ D) :
    (1 - eta) * (partitionComponentSize Q x : ℝ) ≤
      (partitionComponentSize Q (T x) : ℝ) := by
  rw [partitionComponentSize_eq_card_of_mem Q C hC x hx,
    partitionComponentSize_eq_card_of_mem Q D hD (T x) hTx]
  calc
    (1 - eta) * (C.card : ℝ) ≤
      (((C.map T.toEmbedding) ∩ D).card : ℝ) := hoverlap
    _ ≤ (D.card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (Finset.inter_subset_right : (C.map T.toEmbedding) ∩ D ⊆ D)
end SoficGroups

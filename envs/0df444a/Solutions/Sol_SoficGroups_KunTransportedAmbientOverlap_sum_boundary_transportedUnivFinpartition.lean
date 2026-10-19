-- Prove2me | solution 1 for SoficGroups.KunTransportedAmbientOverlap.sum_boundary_transportedUnivFinpartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/6938e474-5c5c-40a2-9956-2d140b3377fb

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_boundary_conjugate_map

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunTransportedAmbientOverlap
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunTransportedAmbientOverlap
theorem _root_.solution
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (σ : ι → Equiv.Perm V) (T : Equiv.Perm V) :
    (∑ C ∈ (SoficGroups.transportedUnivFinpartition Q T).parts,
      SoficGroups.boundary
        (fun i => T * σ i * T⁻¹) C) =
      ∑ C ∈ Q.parts, SoficGroups.boundary σ C := by
  classical
  rw [SoficGroups.transportedUnivFinpartition_parts]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro C _
    exact boundary_conjugate_map σ T C
  · intro C hC D hD heq
    exact T.finsetCongr.injective heq
end SoficGroups.KunTransportedAmbientOverlap

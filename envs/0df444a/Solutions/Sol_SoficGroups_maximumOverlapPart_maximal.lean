-- Prove2me | solution 1 for SoficGroups.maximumOverlapPart_maximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/63455e81-8a25-4cf2-87ea-bc6831f13873

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (C : Finset V)
    (hC : C.Nonempty) (hCU : C ⊆ U) :
    ∀ E ∈ Q.parts,
      (C ∩ E).card ≤ (C ∩ maximumOverlapPart Q C).card := by
  classical
  have h : C.Nonempty ∧ C ⊆ U := ⟨hC, hCU⟩
  simpa only [maximumOverlapPart, dif_pos h] using
    (exists_maximum_overlap_component Q C hC hCU).choose_spec.2
end SoficGroups

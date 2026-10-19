-- Prove2me | solution 1 for SoficGroups.maximumOverlapPart_overlap_of_not_mem_insufficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/0fe1f763-9911-45cd-b488-0f5e0f1dccac

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
    (P Q : Finpartition U) (eta : ℝ) (C : Finset V)
    (hC : C ∈ P.parts)
    (hretained : C ∉ insufficientOverlapComponents P Q eta) :
    (1 - eta) * (C.card : ℝ) ≤
      ((C ∩ maximumOverlapPart Q C).card : ℝ) := by
  classical
  apply le_of_not_gt
  intro hbad
  apply hretained
  change C ∈ P.parts.filter (fun C =>
    ((C ∩ maximumOverlapPart Q C).card : ℝ) <
      (1 - eta) * (C.card : ℝ))
  exact Finset.mem_filter.mpr ⟨hC, hbad⟩
end SoficGroups

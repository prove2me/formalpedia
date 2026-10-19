-- Prove2me | solution 1 for SoficGroups.SourceProductThroughAlpha.boundary_sourceCompressedGeneratorSubtypeEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/f9dafb43-f1bf-42a6-866d-4296696a76c7

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceProductThroughAlpha
open scoped BigOperators
namespace SoficGroups.SourceProductThroughAlpha
theorem _root_.solution
    {V : Type*} [DecidableEq V]
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (σ : ↥(sourceCompressedGeneratingFinset SΓ) → Equiv.Perm V)
    (E : Finset V) :
    SoficGroups.boundary
      (fun i : ↥SΓ =>
        σ (sourceCompressedGeneratorSubtypeEquiv SΓ i)) E =
      SoficGroups.boundary σ E := by
  classical
  unfold SoficGroups.boundary
  exact Equiv.sum_comp (sourceCompressedGeneratorSubtypeEquiv SΓ)
    (fun i : ↥(sourceCompressedGeneratingFinset SΓ) =>
      (E.filter fun x => σ i x ∉ E).card)
end SoficGroups.SourceProductThroughAlpha

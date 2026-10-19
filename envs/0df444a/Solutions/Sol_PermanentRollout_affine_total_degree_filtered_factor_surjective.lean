-- Prove2me | solution 1 for PermanentRollout.affine_total_degree_filtered_factor_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/d88fbddd-3f9f-496d-ab39-0d5fc4122253

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} {I J : Ideal (MvPolynomial ι ℂ)}
    (hIJ : I ≤ J) (n : ℕ) :
    Function.Surjective (affineTotalDegreeFilteredFactor hIJ n) := by
  intro y
  obtain ⟨p, hp, hpimage⟩ :=
    (affine_total_degree_filtered_piece_mem_iff J n y).mp y.property
  have hpmem : Ideal.Quotient.mk I p ∈
      affineTotalDegreeFilteredPiece I n :=
    (affine_total_degree_filtered_piece_mem_iff
      I n (Ideal.Quotient.mk I p)).mpr ⟨p, hp, rfl⟩
  refine ⟨⟨Ideal.Quotient.mk I p, hpmem⟩, ?_⟩
  apply Subtype.ext
  change Ideal.Quotient.factorₐ ℂ hIJ (Ideal.Quotient.mk I p) =
    (y : MvPolynomial ι ℂ ⧸ J)
  change Ideal.Quotient.mk J p = _
  exact hpimage
end PermanentRollout

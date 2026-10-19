-- Prove2me | solution 1 for PermanentRollout.affine_total_degree_filtered_bot_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/f17f74aa-ef21-44d1-b1d9-235472fd3d2c

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_restrictTotalDegree_finrank

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Fintype ι] (N : ℕ) :
    Module.finrank ℂ
        (affineTotalDegreeFilteredPiece
          (⊥ : Ideal (MvPolynomial ι ℂ)) N) =
      (N + Fintype.card ι).choose (Fintype.card ι) := by
  let q := affineTotalDegreeFilteredProjection
    (⊥ : Ideal (MvPolynomial ι ℂ)) N
  have hmk :
      Function.Injective
        (Ideal.Quotient.mk (⊥ : Ideal (MvPolynomial ι ℂ))) :=
    ((Ideal.Quotient.mk_bijective_iff_eq_bot
      (⊥ : Ideal (MvPolynomial ι ℂ))).mpr rfl).1
  have hqinj : Function.Injective q := by
    intro x y hxy
    apply Subtype.ext
    apply hmk
    have h := congrArg Subtype.val hxy
    exact h
  have hqsurj : Function.Surjective q :=
    affine_total_degree_filtered_projection_surjective
      (⊥ : Ideal (MvPolynomial ι ℂ)) N
  have hequiv := (LinearEquiv.ofBijective q ⟨hqinj, hqsurj⟩).finrank_eq
  calc
    Module.finrank ℂ
        (affineTotalDegreeFilteredPiece
          (⊥ : Ideal (MvPolynomial ι ℂ)) N) =
        Module.finrank ℂ (MvPolynomial.restrictTotalDegree ι ℂ N) :=
      hequiv.symm
    _ = (N + Fintype.card ι).choose (Fintype.card ι) :=
      affine_restrictTotalDegree_finrank N
end PermanentRollout

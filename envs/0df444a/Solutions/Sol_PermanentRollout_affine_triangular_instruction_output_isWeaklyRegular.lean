-- Prove2me | solution 1 for PermanentRollout.affine_triangular_instruction_output_isWeaklyRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/05607203-cde0-4da8-865d-a22579349af9

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_ringEquiv_isWeaklyRegular_ofFn_image
import Theorems.Thm_PermanentRollout_affineTriangularInstructionInputAlgEquiv_mk

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k q : ℕ}
    (rhs : Fin q → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (output : Fin k → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ)
    (hgate : ∀ j, gate j = affineGateGraphEvaluation gate (rhs j))
    (htop : ∀ j i : Fin q,
      Sum.inr i ∈ (rhs j).vars → i.val < j.val)
    (houtput : ∀ i, affineGateGraphEvaluation gate (output i) = F i)
    (hregular : RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin k) ℂ)
        (List.ofFn fun i : Fin k => F i - MvPolynomial.C (target i))) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin k ⊕ Fin q) ℂ ⧸
        affineTriangularInstructionIdeal rhs)
      (List.ofFn fun i : Fin k =>
        Ideal.Quotient.mk (affineTriangularInstructionIdeal rhs)
          (output i - MvPolynomial.C (target i))) := by
  let E := affineTriangularInstructionInputAlgEquiv
    rhs gate hgate htop
  apply homogeneousMap_allRank_ringEquiv_isWeaklyRegular_ofFn_image
    E.toRingEquiv
  have himage : ∀ i : Fin k,
      E (Ideal.Quotient.mk (affineTriangularInstructionIdeal rhs)
        (output i - MvPolynomial.C (target i))) =
          F i - MvPolynomial.C (target i) := by
    intro i
    change affineTriangularInstructionInputAlgEquiv
      rhs gate hgate htop
        (Ideal.Quotient.mk (affineTriangularInstructionIdeal rhs)
          (output i - MvPolynomial.C (target i))) = _
    rw [affineTriangularInstructionInputAlgEquiv_mk]
    simp [houtput i]
  have hfun :
      (fun i : Fin k =>
        E.toRingEquiv
          (Ideal.Quotient.mk (affineTriangularInstructionIdeal rhs)
            (output i - MvPolynomial.C (target i)))) =
        (fun i : Fin k => F i - MvPolynomial.C (target i)) := by
    funext i
    exact himage i
  rw [hfun]
  exact hregular
end PermanentRollout

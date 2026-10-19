-- Prove2me | solution 1 for PermanentRollout.affine_triangular_instruction_output_equations_isWeaklyRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/fc35c3df-ef76-44da-b534-fecf25f40b00

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_triangular_instructions_isWeaklyRegular
import Theorems.Thm_PermanentRollout_affine_triangular_instruction_output_isWeaklyRegular

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
      (MvPolynomial (Fin k ⊕ Fin q) ℂ)
      ((List.ofFn fun j : Fin q =>
          MvPolynomial.X (Sum.inr j) - rhs j) ++
        (List.ofFn fun i : Fin k =>
          output i - MvPolynomial.C (target i))) := by
  classical
  let R := MvPolynomial (Fin k ⊕ Fin q) ℂ
  let I := affineTriangularInstructionIdeal rhs
  let gates : List R := List.ofFn fun j : Fin q =>
    MvPolynomial.X (Sum.inr j) - rhs j
  let outputs : List R := List.ofFn fun i : Fin k =>
    output i - MvPolynomial.C (target i)
  have hgateweak : RingTheory.Sequence.IsWeaklyRegular R gates :=
    affine_triangular_instructions_isWeaklyRegular
      rhs gate hgate htop
  have hlist : Ideal.ofList gates = I := by
    change Ideal.span {p | p ∈ List.ofFn fun j : Fin q =>
      MvPolynomial.X (Sum.inr j) - rhs j} =
      Ideal.span (Set.range fun j : Fin q =>
        MvPolynomial.X (Sum.inr j) - rhs j)
    congr 1
    ext p
    simp
  have hsub :
      (Ideal.ofList gates • (⊤ : Submodule R R)) =
        (I : Submodule R R) := by
    rw [hlist]
    simp
  have houtputquot :
      RingTheory.Sequence.IsWeaklyRegular (R ⧸ I)
        (List.ofFn fun i : Fin k =>
          Ideal.Quotient.mk I
            (output i - MvPolynomial.C (target i))) :=
    affine_triangular_instruction_output_isWeaklyRegular
      rhs gate output F target hgate htop houtput hregular
  have houtputmap :
      RingTheory.Sequence.IsWeaklyRegular (R ⧸ I)
        (outputs.map (algebraMap R (R ⧸ I))) := by
    dsimp only [outputs]
    rw [← List.ofFn_comp']
    change RingTheory.Sequence.IsWeaklyRegular (R ⧸ I)
      (List.ofFn fun i : Fin k =>
        Ideal.Quotient.mk I
          (output i - MvPolynomial.C (target i)))
    exact houtputquot
  have houtputR :
      RingTheory.Sequence.IsWeaklyRegular (R ⧸ I) outputs :=
    (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff
      (R ⧸ I) (R ⧸ I) outputs).mp houtputmap
  change RingTheory.Sequence.IsWeaklyRegular R (gates ++ outputs)
  rw [RingTheory.Sequence.isWeaklyRegular_append_iff]
  refine ⟨hgateweak, ?_⟩
  exact ((Submodule.quotEquivOfEq _ _ hsub).isWeaklyRegular_congr
    outputs).mpr houtputR
end PermanentRollout

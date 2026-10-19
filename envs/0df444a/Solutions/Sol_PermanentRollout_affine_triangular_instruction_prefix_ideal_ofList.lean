-- Prove2me | solution 1 for PermanentRollout.affine_triangular_instruction_prefix_ideal_ofList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/a5df19ad-f662-4954-8097-512511dfd57e

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
    {k q : ℕ}
    (rhs : Fin q → MvPolynomial (Fin k ⊕ Fin q) ℂ) (n : ℕ) :
    Ideal.ofList
        ((List.ofFn fun j : Fin q =>
          MvPolynomial.X (Sum.inr j) - rhs j).take n) =
      affineTriangularInstructionPrefixIdeal rhs n := by
  classical
  change Ideal.span
      {p | p ∈ (List.ofFn fun j : Fin q =>
        MvPolynomial.X (Sum.inr j) - rhs j).take n} =
    Ideal.span (Set.range fun j : {j : Fin q // j.val < n} =>
      MvPolynomial.X (Sum.inr (j : Fin q)) - rhs j)
  congr 1
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi, heq⟩ := List.mem_take_iff_getElem.mp hp
    have hiq : i < q := by
      simpa only [List.length_ofFn] using
        (lt_of_lt_of_le hi (Nat.min_le_right _ _))
    have hin : i < n :=
      lt_of_lt_of_le hi (Nat.min_le_left _ _)
    refine ⟨⟨⟨i, hiq⟩, hin⟩, ?_⟩
    simpa only [List.getElem_ofFn] using heq
  · rintro ⟨⟨i, hi⟩, rfl⟩
    apply List.mem_take_iff_getElem.mpr
    refine ⟨i.val, ?_, ?_⟩
    · simpa only [List.length_ofFn] using (lt_min hi i.isLt)
    · simp
end PermanentRollout

-- Prove2me | solution 1 for PermanentRollout.affine_triangular_instructions_isWeaklyRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/6efe241a-3b33-46d4-9ea0-3519cc6ef625

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_instruction_isSMulRegular_mod_prefix_graph
import Theorems.Thm_PermanentRollout_affine_triangular_instruction_prefix_ideal_ofList

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
    (hgate : ∀ j, gate j = affineGateGraphEvaluation gate (rhs j))
    (htop : ∀ j i : Fin q,
      Sum.inr i ∈ (rhs j).vars → i.val < j.val) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin k ⊕ Fin q) ℂ)
      (List.ofFn fun j : Fin q =>
        MvPolynomial.X (Sum.inr j) - rhs j) := by
  classical
  constructor
  intro n hn
  have hnq : n < q := by
    simpa only [List.length_ofFn] using hn
  let j : Fin q := ⟨n, hnq⟩
  let R := MvPolynomial (Fin k ⊕ Fin q) ℂ
  let I := affineGatePrefixGraphIdeal gate n
  have hsub :
      (Ideal.ofList
        ((List.ofFn fun i : Fin q =>
          MvPolynomial.X (Sum.inr i) - rhs i).take n) •
          (⊤ : Submodule R R)) = (I : Submodule R R) := by
    rw [affine_triangular_instruction_prefix_ideal_ofList rhs n,
      affine_triangular_instruction_prefix_ideal_eq_graph
        rhs gate hgate htop n]
    simp [I]
  have hreg : IsSMulRegular (R ⧸ I)
      (MvPolynomial.X (Sum.inr j) - rhs j) :=
    affine_instruction_isSMulRegular_mod_prefix_graph
      gate rhs j (htop j) (hgate j)
  have htransport :=
    ((Submodule.quotEquivOfEq _ _ hsub).isSMulRegular_congr
      (MvPolynomial.X (Sum.inr j) - rhs j)).mpr hreg
  simpa only [List.getElem_ofFn] using htransport
end PermanentRollout

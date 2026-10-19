-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_finSucc_lastCoordinate_isSMulRegular_of_slice_weaklyRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/2ec5cefe-297e-40e7-8e4e-bfeb22553447

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_rollout_idealOfVars_isMaximal
import Theorems.Thm_PermanentRollout_isSMulRegular_of_maximal_radical_and_regular_witness
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_fin_hyperplane_isSMulRegular_of_quotient_weaklyRegular

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {n : ℕ}
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ)
    (hzero : ∀ point : Fin (n + 1) → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (c : Fin (n + 1) → ℂ)
    (j : Fin (n + 1)) (hj : c j ≠ 0)
    (hregular :
      RingTheory.Sequence.IsWeaklyRegular
        (MvPolynomial (Fin (n + 1)) ℂ ⧸
          Ideal.span
            ({permanentRolloutLinearCoordinateCombination (n + 1) c} :
              Set (MvPolynomial (Fin (n + 1)) ℂ)))
        (List.ofFn fun i : Fin n =>
          Ideal.Quotient.mk
            (Ideal.span
              ({permanentRolloutLinearCoordinateCombination (n + 1) c} :
                Set (MvPolynomial (Fin (n + 1)) ℂ)))
            (F i.castSucc))) :
    IsSMulRegular
      (MvPolynomial (Fin (n + 1)) ℂ ⧸
        Ideal.span (Set.range fun i : Fin n => F i.castSucc))
      (F (Fin.last n)) := by
  classical
  let I : Ideal (MvPolynomial (Fin (n + 1)) ℂ) :=
    Ideal.span (Set.range fun i : Fin n => F i.castSucc)
  let ell : MvPolynomial (Fin (n + 1)) ℂ :=
    permanentRolloutLinearCoordinateCombination (n + 1) c
  have hell : ell ≠ 0 := by
    intro hz
    have hev := congrArg
      (MvPolynomial.eval (Pi.single j (1 : ℂ))) hz
    apply hj
    simpa [ell, permanentRolloutLinearCoordinateCombination,
      Pi.single_apply, mul_ite] using hev
  have hellvertex : ell ∈ MvPolynomial.idealOfVars (Fin (n + 1)) ℂ := by
    change
      (∑ i : Fin (n + 1), c i • MvPolynomial.X i) ∈
        MvPolynomial.idealOfVars (Fin (n + 1)) ℂ
    apply Ideal.sum_mem
    intro i _
    rw [MvPolynomial.smul_eq_C_mul]
    apply (MvPolynomial.idealOfVars (Fin (n + 1)) ℂ).mul_mem_left
    exact Ideal.subset_span (Set.mem_range_self i)
  have hellregular : IsSMulRegular
      (MvPolynomial (Fin (n + 1)) ℂ ⧸ I) ell := by
    exact homogeneousMap_allRank_fin_hyperplane_isSMulRegular_of_quotient_weaklyRegular
      (fun i : Fin n => F i.castSucc) ell hell hregular
  have hgen (i : Fin (n + 1)) : F i ∈ homogeneousMapIdeal F := by
    rw [homogeneousMapIdeal]
    exact Ideal.subset_span (Set.mem_range_self i)
  have hfull :
      I ⊔ Ideal.span
        ({F (Fin.last n)} : Set (MvPolynomial (Fin (n + 1)) ℂ)) =
      homogeneousMapIdeal F := by
    apply le_antisymm
    · apply sup_le
      · change Ideal.span (Set.range fun i : Fin n => F i.castSucc) ≤ _
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact hgen i.castSucc
      · rw [Ideal.span_le]
        simpa using hgen (Fin.last n)
    · rw [homogeneousMapIdeal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨q, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
      · exact Ideal.mem_sup_left
          (Ideal.subset_span (Set.mem_range_self q))
      · exact Ideal.mem_sup_right
          (Ideal.subset_span (Set.mem_singleton _))
  apply isSMulRegular_of_maximal_radical_and_regular_witness
    I (F (Fin.last n)) ell
    (MvPolynomial.idealOfVars (Fin (n + 1)) ℂ)
    (permanent_rollout_idealOfVars_isMaximal (n + 1))
  · rw [hfull]
    exact radical_homogeneousMapIdeal_eq_idealOfVars F hzero
  · exact hellvertex
  · exact hellregular
end PermanentRollout

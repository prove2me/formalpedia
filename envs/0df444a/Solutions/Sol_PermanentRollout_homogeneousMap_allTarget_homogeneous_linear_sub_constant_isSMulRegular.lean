-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_homogeneous_linear_sub_constant_isSMulRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/72f7c883-9a5f-44bd-98c9-6ebf7922fa1f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_totalDegree_sub_homogeneousComponent_le

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
open scoped Pointwise
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*}
    (I : Ideal (MvPolynomial ι ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι ℂ))
    (t : MvPolynomial ι ℂ)
    (ht : t.IsHomogeneous 1)
    (htregular : IsSMulRegular (MvPolynomial ι ℂ ⧸ I) t)
    (c : ℂ) :
    IsSMulRegular (MvPolynomial ι ℂ ⧸ I)
      (t - MvPolynomial.C c) := by
  classical
  have htcolon :=
    (isSMulRegular_quotient_iff_mem_of_smul_mem I t).mp htregular
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem I
    (t - MvPolynomial.C c)).mpr
  intro p hp
  have hp' : (t - MvPolynomial.C c) * p ∈ I := by
    simpa [smul_eq_mul] using hp
  have haux : ∀ n : ℕ, ∀ q : MvPolynomial ι ℂ,
      q.totalDegree ≤ n →
      (t - MvPolynomial.C c) * q ∈ I → q ∈ I := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hq hproduct
      have hcomp := MvPolynomial.homogeneousComponent_mem_of_mem
        hI hproduct (n + 1)
      have hqhigh : MvPolynomial.homogeneousComponent (n + 1) q = 0 :=
        MvPolynomial.homogeneousComponent_eq_zero (n + 1) q (by omega)
      rw [sub_mul, map_sub, mul_comm t q,
        homogeneousComponent_mul_of_right_isHomogeneous q t ht
          (by omega),
        MvPolynomial.homogeneousComponent_C_mul,
        hqhigh,
        mul_zero, sub_zero] at hcomp
      have htop : MvPolynomial.homogeneousComponent n q ∈ I := by
        apply htcolon (MvPolynomial.homogeneousComponent n q)
        simpa [smul_eq_mul, mul_comm] using hcomp
      by_cases hn : n = 0
      · subst n
        have hqzero : q.totalDegree = 0 := Nat.eq_zero_of_le_zero hq
        have hsum : MvPolynomial.homogeneousComponent 0 q = q := by
          simpa only [hqzero, zero_add,
            Finset.sum_range_succ, Finset.sum_range_zero, zero_add] using
            (MvPolynomial.sum_homogeneousComponent q)
        exact hsum ▸ htop
      · let q' := q - MvPolynomial.homogeneousComponent n q
        have hdegree : q'.totalDegree < n := by
          have hbound :=
            homogeneousMap_allTarget_totalDegree_sub_homogeneousComponent_le q hq
          change (q - MvPolynomial.homogeneousComponent n q).totalDegree < n
          omega
        have hq' : (t - MvPolynomial.C c) * q' ∈ I := by
          change (t - MvPolynomial.C c) *
            (q - MvPolynomial.homogeneousComponent n q) ∈ I
          rw [mul_sub]
          exact I.sub_mem hproduct
            (I.mul_mem_left (t - MvPolynomial.C c) htop)
        have hq'mem : q' ∈ I :=
          ih q'.totalDegree hdegree q' (le_refl _) hq'
        have hdecomp : q' + MvPolynomial.homogeneousComponent n q = q := by
          dsimp [q']
          ring
        rw [← hdecomp]
        exact I.add_mem hq'mem htop
  exact haux p.totalDegree p (le_refl _) hp'
end PermanentRollout

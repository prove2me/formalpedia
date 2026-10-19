-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_fin_hyperplane_isSMulRegular_of_quotient_weaklyRegular_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/c2734169-c790-46ff-b056-1bcde0305518

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_weaklyRegular_fin_syzygy_lifts_aux

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
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (f : Fin n → R) (ell : R) (hell : ell ≠ 0)
    (hregular :
      RingTheory.Sequence.IsWeaklyRegular
        (R ⧸ Ideal.span ({ell} : Set R))
        (List.ofFn fun i : Fin n =>
          Ideal.Quotient.mk (Ideal.span ({ell} : Set R)) (f i))) :
    IsSMulRegular (R ⧸ Ideal.span (Set.range f)) ell := by
  classical
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem
    (Ideal.span (Set.range f)) ell).mpr
  intro p hp
  have hp' : ell * p ∈ Ideal.span (Set.range f) := by
    simpa [smul_eq_mul] using hp
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp'
  let J : Ideal R := Ideal.span ({ell} : Set R)
  let q : R →+* R ⧸ J := Ideal.Quotient.mk J
  have hrelation : (∑ i : Fin n, q (a i) * q (f i)) = 0 := by
    calc
      (∑ i : Fin n, q (a i) * q (f i)) =
          q (∑ i : Fin n, a i * f i) := by simp
      _ = q (ell * p) := congrArg q ha
      _ = 0 := by
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        exact J.mul_mem_right p
          (Ideal.subset_span (Set.mem_singleton ell))
  obtain ⟨b, hb, hbsum⟩ :=
    homogeneousMap_allRank_weaklyRegular_fin_syzygy_lifts_aux
      q Ideal.Quotient.mk_surjective n f hregular
      (fun i => q (a i)) hrelation
  have hdiff (i : Fin n) : a i - b i ∈ J := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem (a i) (b i)).mp
    exact (hb i).symm
  choose d hd using fun i : Fin n =>
    Ideal.mem_span_singleton'.mp (hdiff i)
  apply Ideal.mem_span_range_iff_exists_fun.mpr
  refine ⟨d, ?_⟩
  apply mul_left_cancel₀ hell
  calc
    ell * (∑ i : Fin n, d i * f i) =
        ∑ i : Fin n, (d i * ell) * f i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ i : Fin n, (a i - b i) * f i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hd i]
    _ = (∑ i : Fin n, a i * f i) -
        (∑ i : Fin n, b i * f i) := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
    _ = ell * p := by rw [ha, hbsum, sub_zero]
end PermanentRollout

-- Prove2me | solution 1 for PermanentRollout.affine_isSMulRegular_sup_span_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/3989fe8d-2300-4cc1-84cd-3eb68d9fcadb

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
    {R : Type*} [CommRing R]
    (I : Ideal R) (f ell : R)
    (hf : IsSMulRegular (R ⧸ I) f)
    (hell : IsSMulRegular (R ⧸
      (I ⊔ Ideal.span ({f} : Set R))) ell) :
    IsSMulRegular (R ⧸
      (I ⊔ Ideal.span ({ell} : Set R))) f := by
  classical
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem
    (I ⊔ Ideal.span ({ell} : Set R)) f).mpr
  intro p hp
  have hfp : f * p ∈ I ⊔ Ideal.span ({ell} : Set R) := by
    simpa [smul_eq_mul] using hp
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hfp
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hb
  have hrel : f * p = a + ell * q := by
    calc
      f * p = a + b := hab.symm
      _ = a + ell * q := by rw [← hq]; ring
  have hellq : ell * q ∈ I ⊔ Ideal.span ({f} : Set R) := by
    have hrewrite : ell * q = f * p - a := by rw [hrel]; ring
    rw [hrewrite]
    apply (I ⊔ Ideal.span ({f} : Set R)).sub_mem
    · exact (I ⊔ Ideal.span ({f} : Set R)).mul_mem_right p
        (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton f)))
    · exact Ideal.mem_sup_left ha
  have hqmem : q ∈ I ⊔ Ideal.span ({f} : Set R) := by
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem
      (I ⊔ Ideal.span ({f} : Set R)) ell).mp hell
    simpa [smul_eq_mul] using hellq
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hqmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hv
  have hqdecomp : q = u + f * r := by
    calc
      q = u + v := huv.symm
      _ = u + f * r := by rw [← hr]; ring
  have hsmall : f * (p - ell * r) ∈ I := by
    have hrewrite : f * (p - ell * r) = a + ell * u := by
      calc
        f * (p - ell * r) = f * p - f * ell * r := by ring
        _ = a + ell * q - f * ell * r := by rw [hrel]
        _ = a + ell * u := by rw [hqdecomp]; ring
    rw [hrewrite]
    exact I.add_mem ha (I.mul_mem_left ell hu)
  have hpminus : p - ell * r ∈ I := by
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem I f).mp hf
    simpa [smul_eq_mul] using hsmall
  have hdecomp : p = (p - ell * r) + ell * r := by ring
  rw [hdecomp]
  apply (I ⊔ Ideal.span ({ell} : Set R)).add_mem
  · exact Ideal.mem_sup_left hpminus
  · apply Ideal.mem_sup_right
    exact (Ideal.span ({ell} : Set R)).mul_mem_right r
      (Ideal.subset_span (Set.mem_singleton ell))
end PermanentRollout

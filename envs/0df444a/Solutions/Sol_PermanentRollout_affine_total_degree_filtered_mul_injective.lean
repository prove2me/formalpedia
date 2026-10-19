-- Prove2me | solution 1 for PermanentRollout.affine_total_degree_filtered_mul_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/517052bf-df74-4c86-8150-fe3a1b63592f

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
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ))
    (g : MvPolynomial ι ℂ)
    (hregular : IsSMulRegular (MvPolynomial ι ℂ ⧸ I) g)
    (n : ℕ) :
    Function.Injective (affineTotalDegreeFilteredMul I g n) := by
  intro x y hxy
  apply Subtype.ext
  have h := congrArg Subtype.val hxy
  change Ideal.Quotient.mk I g * (x : MvPolynomial ι ℂ ⧸ I) =
    Ideal.Quotient.mk I g * (y : MvPolynomial ι ℂ ⧸ I) at h
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective
    ((x : MvPolynomial ι ℂ ⧸ I) - (y : MvPolynomial ι ℂ ⧸ I))
  have hprod : g * p ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul, hp, mul_sub, sub_eq_zero]
    exact h
  have hpI : p ∈ I := by
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem I g).mp hregular p
    simpa [smul_eq_mul] using hprod
  apply sub_eq_zero.mp
  rw [← hp]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hpI
end PermanentRollout

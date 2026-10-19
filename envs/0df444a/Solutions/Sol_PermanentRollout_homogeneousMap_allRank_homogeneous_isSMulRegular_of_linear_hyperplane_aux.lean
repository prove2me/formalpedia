-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_homogeneous_isSMulRegular_of_linear_hyperplane_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/7f8321ab-f50b-4fdd-9116-42f72d26cc60

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousComponent_mul_of_right_isHomogeneous_of_lt

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
    {ι : Type*}
    (I : Ideal (MvPolynomial ι ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι ℂ))
    (f ell : MvPolynomial ι ℂ) {e : ℕ}
    (hf : f.IsHomogeneous e)
    (hellhom : ell.IsHomogeneous 1)
    (hellregular : IsSMulRegular (MvPolynomial ι ℂ ⧸ I) ell)
    (hfmod : IsSMulRegular
      (MvPolynomial ι ℂ ⧸
        (I ⊔ Ideal.span ({ell} : Set (MvPolynomial ι ℂ)))) f) :
    IsSMulRegular (MvPolynomial ι ℂ ⧸ I) f := by
  classical
  have hellcolon :=
    (isSMulRegular_quotient_iff_mem_of_smul_mem I ell).mp hellregular
  have hfcolon :=
    (isSMulRegular_quotient_iff_mem_of_smul_mem
      (I ⊔ Ideal.span ({ell} : Set (MvPolynomial ι ℂ))) f).mp hfmod
  have homogeneous_aux : ∀ m : ℕ,
      ∀ p : MvPolynomial ι ℂ,
        p.IsHomogeneous m → f * p ∈ I → p ∈ I := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro p hp hfp
      have hpmod : p ∈
          I ⊔ Ideal.span ({ell} : Set (MvPolynomial ι ℂ)) := by
        apply hfcolon p
        change f * p ∈ I ⊔ Ideal.span ({ell} : Set _)
        exact Ideal.mem_sup_left hfp
      obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp hpmod
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hw
      have hdecomp : v + r * ell = p := by simpa [hr] using hvw
      have hvcomponent : MvPolynomial.homogeneousComponent m v ∈ I :=
        MvPolynomial.homogeneousComponent_mem_of_mem hI hv m
      by_cases hm : m = 0
      · subst m
        have hzero :
            MvPolynomial.homogeneousComponent 0 (r * ell) = 0 :=
          homogeneousComponent_mul_of_right_isHomogeneous_of_lt
            r ell hellhom (by omega)
        have hcomp := congrArg
          (MvPolynomial.homogeneousComponent 0) hdecomp
        rw [map_add, hzero, add_zero,
          MvPolynomial.homogeneousComponent_eq_self hp] at hcomp
        exact hcomp ▸ hvcomponent
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        let r' := MvPolynomial.homogeneousComponent (m - 1) r
        have hrhom : r'.IsHomogeneous (m - 1) :=
          MvPolynomial.homogeneousComponent_isHomogeneous (m - 1) r
        have hcomp := congrArg
          (MvPolynomial.homogeneousComponent m) hdecomp
        rw [map_add,
          homogeneousComponent_mul_of_right_isHomogeneous
            r ell hellhom (by omega),
          MvPolynomial.homogeneousComponent_eq_self hp] at hcomp
        change MvPolynomial.homogeneousComponent m v + r' * ell = p
          at hcomp
        have hfr' : f * r' ∈ I := by
          apply hellcolon (f * r')
          change ell * (f * r') ∈ I
          have hfv : f * MvPolynomial.homogeneousComponent m v ∈ I :=
            I.mul_mem_left f hvcomponent
          have hsubtract : f * p -
              f * MvPolynomial.homogeneousComponent m v ∈ I :=
            I.sub_mem hfp hfv
          convert hsubtract using 1
          rw [← hcomp]
          ring
        have hr'I : r' ∈ I := ih (m - 1) (by omega) r' hrhom hfr'
        rw [← hcomp]
        exact I.add_mem hvcomponent (I.mul_mem_right ell hr'I)
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem I f).mpr
  intro p hp
  have hp' : f * p ∈ I := by simpa [smul_eq_mul] using hp
  apply (MvPolynomial.mem_iff_homogeneousComponent_mem hI p).mpr
  intro m
  apply homogeneous_aux m (MvPolynomial.homogeneousComponent m p)
    (MvPolynomial.homogeneousComponent_isHomogeneous m p)
  have hcomponent :=
    MvPolynomial.homogeneousComponent_mem_of_mem hI hp' (e + m)
  rw [mul_comm f p,
    homogeneousComponent_mul_of_right_isHomogeneous p f hf
      (by omega)] at hcomponent
  simpa [Nat.add_sub_cancel_left, mul_comm] using hcomponent
end PermanentRollout

-- Prove2me | solution 1 for PDivisibleGroup.eq_of_forall_point_toAlgHom_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b8e9eb6d-56d6-53ff-87c0-9c7ada2bff89

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Theorems.Thm_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_eq_of_forall_point_toAlgHom_apply_eq

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)]
    (hinj : Function.Injective (algebraMap O (AlgebraicClosure ℚ)))
    {h : ℕ} (H : PDivisibleGroup O p h) (v : ℕ) (a b : H.level v)
    (hab : ∀ x : H.Point (AlgebraicClosure ℚ) v,
      PDivisibleGroup.Point.toAlgHom x a = PDivisibleGroup.Point.toAlgHom x b) :
    a = b := by
  classical
  let K : Type := FractionRing O

  let j : K →ₐ[O] AlgebraicClosure ℚ :=
    IsFractionRing.liftAlgHom (K := K) (g := Algebra.ofId O (AlgebraicClosure ℚ)) hinj
  letI : Algebra K (AlgebraicClosure ℚ) := (j : K →+* AlgebraicClosure ℚ).toAlgebra
  haveI : IsScalarTower O K (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm

  haveI : CharZero K := RingHom.charZero (j : K →+* AlgebraicClosure ℚ)

  haveI : IsReduced (K ⊗[O] H.level v) :=
    HopfAlgebra.isReduced_of_finiteType_of_charZero K (K ⊗[O] H.level v)

  haveI : NoZeroSMulDivisors O (H.level v) := by
    refine noZeroSMulDivisors_iff_right_eq_zero_of_smul.2 fun r hr m hrm => ?_
    have hreg : IsSMulRegular (H.level v) r := Module.IsTorsionFree.isSMulRegular (IsRegular.of_ne_zero hr)
    exact hreg (show r • m = r • 0 by rw [hrm, smul_zero])
  have key := Algebra.eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct K (AlgebraicClosure ℚ)
    (a - b) fun φ => by
      rw [map_sub, sub_eq_zero]
      exact hab (PDivisibleGroup.Point.ofAlgHom φ)
  exact sub_eq_zero.1 key

end S_PDivisibleGroup_eq_of_forall_point_toAlgHom_apply_eq
end P2MW
export P2MW.S_PDivisibleGroup_eq_of_forall_point_toAlgHom_apply_eq (solution)

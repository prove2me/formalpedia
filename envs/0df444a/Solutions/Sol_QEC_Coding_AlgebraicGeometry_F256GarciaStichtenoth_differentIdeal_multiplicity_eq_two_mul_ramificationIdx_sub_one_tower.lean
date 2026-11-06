-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.differentIdeal_multiplicity_eq_two_mul_ramificationIdx_sub_one_tower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:59:55.28612+00:00
-- url     : https://prove2.me/submissions/c2824287-5bdd-4cb0-bc03-3e897d458c5c

import Mathlib.RingTheory.DedekindDomain.Different
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_ExponentTower
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_differentIdeal_multiplicity_tower
section
open Module
attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
private theorem two_mul_sub_one_tower_arithmetic
    (e₁ e₂ : ℕ) (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0) :
    2 * (e₂ - 1) + e₂ * (2 * (e₁ - 1)) =
      2 * (e₁ * e₂ - 1) := by
  obtain ⟨e₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he₁
  obtain ⟨e₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he₂
  simp only [Nat.succ_sub_one]
  have hproduct : Nat.succ e₁ * Nat.succ e₂ =
      Nat.succ (e₁ * e₂ + e₁ + e₂) := by
    simp only [Nat.succ_eq_add_one]
    ring
  rw [hproduct, Nat.succ_sub_one]
  simp only [Nat.succ_eq_add_one]
  ring
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open Module
attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (A B C : Type*)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C]
    [IsDomain A] [IsDomain B]
    [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    [Module.IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [FaithfulSMul B C]
    (p : Ideal A) (P : Ideal B) (Q : Ideal C)
    [P.IsPrime] [Q.IsPrime] [P.LiesOver p] [Q.LiesOver P]
    (hp : p ≠ ⊥)
    (hAB : multiplicity P (differentIdeal A B) =
      2 * (p.ramificationIdx' P - 1))
    (hBC : multiplicity Q (differentIdeal B C) =
      2 * (P.ramificationIdx' Q - 1)) :
    multiplicity Q (differentIdeal A C) =
      2 * (p.ramificationIdx' Q - 1) := by
  have hP_ne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  have heAB_ne : p.ramificationIdx' P ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp
  have heBC_ne : P.ramificationIdx' Q ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q hP_ne
  rw [differentIdeal_multiplicity_tower A B C p P Q hp, hAB, hBC,
    Ideal.ramificationIdx_algebra_tower' p P Q]
  exact two_mul_sub_one_tower_arithmetic
    (p.ramificationIdx' P) (P.ramificationIdx' Q) heAB_ne heBC_ne
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

-- Prove2me | solution 1 for QReversal.NearOpt.kraus_adjoint_representation_independent
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T20:09:25.285215+00:00
-- url     : https://prove2.me/submissions/24ce9f99-9c80-4b53-9289-1f568cca54ac

import Definitions.Def_QReversal_NearOpt_Setting
import Mathlib.Tactic.NoncommRing
noncomputable section
open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QNextReversal_kraus_adjoint_representation_independent
variable {n ι ι' : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype ι']

lemma single_update (A : ι → Matrix n n ℂ) (i j x y : n) :
    krausUpdate A (Matrix.single j i (1 : ℂ)) y x =
      ∑ a, A a y j * star (A a x i) := by
  simp only [krausUpdate,Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  have he (z : n) : (A a*Matrix.single j i (1 : ℂ)) y z=
      if z=i then A a y j else 0 := by
    by_cases hz : z=i
    · subst z;simp
    · rw [Matrix.mul_single_apply_of_ne 1 j i y z hz]
      simp [hz]
  rw [Matrix.mul_apply]
  simp only [he,Matrix.conjTranspose_apply,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]


lemma dual_entry (A : ι → Matrix n n ℂ) (Z : Matrix n n ℂ) (i j : n) :
    (∑ a, (A a)ᴴ*Z*A a) i j =
      ∑ x, ∑ y, Z x y*krausUpdate A (Matrix.single j i (1 : ℂ)) y x := by
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,single_update,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (f := fun a x => (star (A a x i)*Z x _) * A a _ j)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem kraus_adjoint_representation_independent
    (A : ι → Matrix n n ℂ) (A' : ι' → Matrix n n ℂ)
    (hAA' : ∀ X : Matrix n n ℂ, krausUpdate A X=krausUpdate A' X) :
    ∀ Z : Matrix n n ℂ, (∑ a, (A a)ᴴ*Z*A a)=(∑ a, (A' a)ᴴ*Z*A' a) := by
  intro Z
  ext i j
  rw [dual_entry,dual_entry]
  simp_rw [hAA']


end QNextReversal_kraus_adjoint_representation_independent

end
open Matrix PeresTerno QReversal.NearOpt
open scoped MatrixOrder ComplexOrder

set_option autoImplicit false

theorem solution {n ι ι' : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype ι']
    (A : ι → Matrix n n ℂ) (A' : ι' → Matrix n n ℂ)
    (hAA' : ∀ X : Matrix n n ℂ, krausUpdate A X=krausUpdate A' X) :
    ∀ Z : Matrix n n ℂ, (∑ a, (A a)ᴴ*Z*A a)=(∑ a, (A' a)ᴴ*Z*A' a) := by
 exact QNextReversal_kraus_adjoint_representation_independent.kraus_adjoint_representation_independent A A' hAA'
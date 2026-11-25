-- Prove2me | solution 1 for QReversal.NearOpt.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T20:10:49.376353+00:00
-- url     : https://prove2.me/submissions/30e06ea4-eda9-4f75-b6e1-ab3ceee9a68c

import Theorems.Thm_QReversal_NearOpt_kraus_adjoint_representation_independent
import Definitions.Def_QReversal_NearOpt_Setting
import Mathlib.Tactic.NoncommRing
noncomputable section
open Matrix PeresTerno
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QNextReversal_reversal_independent
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

lemma reversal_form (A : ι → Matrix n n ℂ) (ρ Y : Matrix n n ℂ) :
    krausUpdate (QReversal.NearOpt.reversal A ρ) Y =
      CFC.sqrt ρ*(∑ a, (A a)ᴴ*
        (QReversal.NearOpt.invSqrt (krausUpdate A ρ)*Y*
          (QReversal.NearOpt.invSqrt (krausUpdate A ρ))ᴴ)*A a)*(CFC.sqrt ρ)ᴴ := by
  simp only [krausUpdate,QReversal.NearOpt.reversal,conjTranspose_mul,conjTranspose_conjTranspose,
    Matrix.mul_sum,Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Matrix.mul_assoc]

theorem reversal_independent (A : ι → Matrix n n ℂ) (A' : ι' → Matrix n n ℂ)
    (hAA' : ∀ X : Matrix n n ℂ, krausUpdate A X=krausUpdate A' X)
    (ρ : Matrix n n ℂ) :
    ∀ Y : Matrix n n ℂ,
      krausUpdate (QReversal.NearOpt.reversal A ρ) Y =
        krausUpdate (QReversal.NearOpt.reversal A' ρ) Y := by
  intro Y
  rw [reversal_form,reversal_form,hAA' ρ,
    QReversal.NearOpt.kraus_adjoint_representation_independent A A' hAA']
end QNextReversal_reversal_independent

end
open Matrix PeresTerno QReversal.NearOpt
open scoped MatrixOrder ComplexOrder

set_option autoImplicit false



theorem solution {n ι ι' : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype ι']
    (A : ι → Matrix n n ℂ) (A' : ι' → Matrix n n ℂ)
    (hAA' : ∀ X : Matrix n n ℂ, krausUpdate A X = krausUpdate A' X)
    (ρ : Matrix n n ℂ) (hρ : IsDensityMatrix ρ) (hfull : (krausUpdate A ρ).PosDef) :
    ∀ Y : Matrix n n ℂ, krausUpdate (reversal A ρ) Y = krausUpdate (reversal A' ρ) Y := by
 exact QNextReversal_reversal_independent.reversal_independent A A' hAA' ρ
-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.conjugate_linearization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T23:10:40.576833+00:00
-- url     : https://prove2.me/submissions/84074e6d-d093-4924-9860-cc82a5dff71f

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

attribute [local instance] Classical.propDecidable Classical.decEq

theorem X7C11_next_eq {p : ℕ} (i : Fin p) : cyclicNext i = finRotate p i := by
  cases p with
  | zero => exact i.elim0
  | succ n =>
    rw [finRotate_apply]; ext; simp [cyclicNext, Fin.val_add]

theorem X7C11_dual_single {A B K : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype K] (F : K → Matrix B A ℂ) (u v : B) (a b : A) :
    operatorTraceDual (krausApply F) (Matrix.single u v 1) a b =
      ∑ k, F k v b * conj (F k u a) := by
  simp [operatorTraceDual, krausApply, Matrix.trace, Matrix.mul_apply, Matrix.single_apply,
    Matrix.sum_apply, Finset.sum_mul, Matrix.conjTranspose_apply]
  simp only [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']


theorem X7C11_E1 {A B K : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype K] (F : K → Matrix B A ℂ) (p : ℕ) (a b : Fin p → A) :
    channelLinearizer (krausApply F) p a b =
      ∑ x : Fin p → B, ∏ i, ∑ k, F k (x i) (b i) * conj (F k (x (cyclicNext i)) (a i)) := by
  simp only [channelLinearizer, piSuperop, leftCycle, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact X7C11_dual_single F _ _ _ _


theorem X7C11_E3 {A B K : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype K] (F : K → Matrix B A ℂ) (p : ℕ) (a b : Fin p → A) :
    (krausLinearizer (rowKraus F) p)ᴴ a b =
      ∑ x : Fin p → B, ∏ i, ∑ k, F k (x i) (b i) * conj (F k (x (cyclicNext i)) (a i)) := by
  simp only [Matrix.conjTranspose_apply, krausLinearizer, rowKraus, star_sum, star_prod,
    Matrix.mul_apply, star_mul', Matrix.conjTranspose_apply, star_star]
  refine Finset.sum_congr rfl (fun x _ => Finset.prod_congr rfl (fun i _ =>
    Finset.sum_congr rfl (fun k _ => ?_)))
  simp

theorem X7C11_E2 {A B K : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype K] (F : K → Matrix B A ℂ) (p : ℕ) (a b : Fin p → A) :
    (krausLinearizer F p * leftCycle A p) a b =
      ∑ ks : Fin p → K, ∏ i, ∑ y, conj (F (ks i) y (a i)) * F (ks (cyclicNext i)) y (b (cyclicNext i)) := by
  simp only [Matrix.mul_apply, leftCycle, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, krausLinearizer, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rfl


theorem X7C11_main {A B K : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype K] [DecidableEq K] (F : K → Matrix B A ℂ) (p : ℕ) :
    channelLinearizer (krausApply F) p = (krausLinearizer (rowKraus F) p)ᴴ ∧
    channelLinearizer (krausApply F) p = krausLinearizer F p * leftCycle A p := by
  refine ⟨?_, ?_⟩
  · ext a b
    rw [X7C11_E1, X7C11_E3]
  · ext a b
    rw [X7C11_E1, X7C11_E2]
    simp only [X7C11_next_eq]
    simp_rw [Fintype.prod_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ks _ => ?_)
    refine Fintype.sum_equiv (Equiv.arrowCongr (finRotate p).symm (Equiv.refl B)) _ _ ?_
    intro x
    simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.comp_apply, id]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, mul_comm]
    congr 1
    exact (Equiv.prod_comp (finRotate p) (fun j => F (ks j) (x j) (b j))).symm

end QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Claimed50.P48
open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)
open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)
open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)
open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P36 in
theorem solution {A B K : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype K] [DecidableEq K] [Nonempty A] [Nonempty B] [Nonempty K]
    (F : K → Matrix B A ℂ) (hF : IsKrausFamily F) (p : ℕ) (hp : 1 ≤ p) :
    channelLinearizer (krausApply F) p = (krausLinearizer (rowKraus F) p)ᴴ ∧
    channelLinearizer (krausApply F) p = krausLinearizer F p * leftCycle A p :=
  X7C11_main F p

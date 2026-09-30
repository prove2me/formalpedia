-- Prove2me | solution 1 for TranscendenceTheory.small_integral_coordinates_of_bivariate_values
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T04:05:58.609171+00:00
-- url     : https://prove2.me/submissions/da5955b0-581d-4117-ac61-c29fb0dce3ec

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Normed.Ring.Int
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.PowerBasis
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Convert

open Polynomial Module
open scoped Polynomial

namespace TranscendenceTheory.IntegralNorm

noncomputable def length (p : ℤ[X]) : ℝ := p.sum fun _ a ↦ ‖a‖

lemma length_nonneg (p : ℤ[X]) : 0 ≤ length p :=
  Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

lemma length_eq_sum_range (p : ℤ[X]) (D : ℕ) (hD : p.natDegree < D) :
    length p = ∑ k ∈ Finset.range D, ‖p.coeff k‖ := by
  exact Polynomial.sum_eq_of_subset _ (fun _ ↦ norm_zero) (by
    intro k hk
    exact Finset.mem_range.mpr ((le_natDegree_of_mem_supp k hk).trans_lt hD))

lemma length_zero : length 0 = 0 := by simp [length]

lemma length_monomial (k : ℕ) (a : ℤ) : length (monomial k a) = ‖a‖ := by
  simp [length]

lemma length_add_le (p q : ℤ[X]) : length (p + q) ≤ length p + length q := by
  let D := max p.natDegree q.natDegree + 1
  rw [length_eq_sum_range (p + q) D (lt_of_le_of_lt (natDegree_add_le p q) (by omega)),
    length_eq_sum_range p D (by omega), length_eq_sum_range q D (by omega),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ ↦ by simpa using norm_add_le (p.coeff k) (q.coeff k)

lemma length_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) :
    length (∑ i ∈ s, f i) ≤ ∑ i ∈ s, length (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [length_zero]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (length_add_le _ _).trans (add_le_add_right ih _)

lemma length_mul_le (p q : ℤ[X]) : length (p * q) ≤ length p * length q := by
  rw [Polynomial.mul_eq_sum_sum]
  calc
    _ ≤ ∑ i ∈ p.support, length (q.sum fun j b ↦ monomial (i + j) (p.coeff i * b)) :=
      length_sum_le _ _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, ‖p.coeff i‖ * ‖q.coeff j‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Polynomial.sum_def, length_monomial, norm_mul] using
        length_sum_le q.support (fun j ↦ monomial (i + j) (p.coeff i * q.coeff j))
    _ = _ := by
      simp only [length, Polynomial.sum_def, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm

lemma length_one : length 1 = 1 := by
  simpa using length_monomial 0 1

lemma length_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) :
    length (∏ i ∈ s, f i) ≤ ∏ i ∈ s, length (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [length_one]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (length_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (length_nonneg _))

lemma norm_coeff_le_length (p : ℤ[X]) (k : ℕ) : ‖p.coeff k‖ ≤ length p := by
  by_cases hk : k ∈ p.support
  · exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) hk
  · simp only [(Polynomial.notMem_support_iff.mp hk), norm_zero]
    exact length_nonneg p

lemma length_le_of_coeff_le (p : ℤ[X]) (H : ℝ) (hH : ∀ k, ‖p.coeff k‖ ≤ H) :
    length p ≤ (p.natDegree + 1 : ℝ) * H := by
  rw [length_eq_sum_range p (p.natDegree + 1) (by omega)]
  calc
    _ ≤ ∑ _k ∈ Finset.range (p.natDegree + 1), H := Finset.sum_le_sum fun k _ ↦ hH k
    _ = _ := by simp

end TranscendenceTheory.IntegralNorm

open Polynomial Module
open scoped Polynomial

namespace TranscendenceTheory.IntegralCoordinates

open IntegralNorm

variable {S : Type*} [CommRing S] [Algebra ℤ[X] S]
variable {d : ℕ} (b : Basis (Fin (d + 1)) ℤ[X] S)

lemma repr_mul (x y : S) (i : Fin (d + 1)) :
    b.repr (y * x) i = ∑ j, b.repr y j * b.repr (b j * x) i := by
  conv_lhs => arg 1; arg 2; arg 1; rw [← b.sum_repr y]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]

lemma power_degree_bound (hb : b 0 = 1) (x : S) (K : ℕ)
    (hK : ∀ i j, (b.repr (b j * x) i).natDegree ≤ K) (m : ℕ) :
    ∀ i, (b.repr (x ^ m) i).natDegree ≤ K * m := by
  induction m with
  | zero =>
    intro i
    rw [pow_zero, ← hb, b.repr_self_apply]
    split_ifs <;> simp
  | succ m ih =>
    intro i
    rw [pow_succ, repr_mul]
    apply natDegree_sum_le_of_forall_le
    intro j _
    exact natDegree_mul_le.trans (by simpa [Nat.mul_succ] using Nat.add_le_add (ih j) (hK i j))

lemma power_length_bound (hb : b 0 = 1) (x : S) (K : ℝ) (hK₀ : 0 ≤ K)
    (hK : ∀ i j, length (b.repr (b j * x) i) ≤ K) (m : ℕ) :
    ∀ i, length (b.repr (x ^ m) i) ≤ ((d + 1) * K) ^ m := by
  induction m with
  | zero =>
    intro i
    rw [pow_zero, ← hb, b.repr_self_apply, pow_zero]
    split_ifs <;> simp [length_one, length_zero]
  | succ m ih =>
    intro i
    rw [pow_succ, repr_mul]
    calc
      _ ≤ ∑ j, length (b.repr (x ^ m) j * b.repr (b j * x) i) := length_sum_le _ _
      _ ≤ ∑ _j : Fin (d + 1), ((d + 1) * K) ^ m * K := by
        apply Finset.sum_le_sum
        intro j _
        exact (length_mul_le _ _).trans
          (mul_le_mul (ih j) (hK i j) (length_nonneg _) (by positivity))
      _ = _ := by simp [pow_succ]; ring

lemma repr_aeval (x : S) (P : ℤ[X][X]) (i : Fin (d + 1)) :
    b.repr (aeval x P) i =
      ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * b.repr (x ^ j) i := by
  rw [aeval_eq_sum_range]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]

lemma eval_degree_bound (hb : b 0 = 1) (x : S) (K D E : ℕ)
    (hK : ∀ i j, (b.repr (b j * x) i).natDegree ≤ K)
    (P : ℤ[X][X]) (hE : P.natDegree ≤ E)
    (hD : ∀ j, (P.coeff j).natDegree ≤ D) (i : Fin (d + 1)) :
    (b.repr (aeval x P) i).natDegree ≤ D + K * E := by
  rw [repr_aeval]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hjE : j ≤ E := (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hE
  exact natDegree_mul_le.trans
    (Nat.add_le_add (hD j) ((power_degree_bound b hb x K hK j i).trans
      (Nat.mul_le_mul_left K hjE)))

lemma eval_length_bound (hb : b 0 = 1) (x : S) (K H : ℝ) (E : ℕ)
    (hK : 1 ≤ K) (hH : 0 ≤ H)
    (hM : ∀ i j, length (b.repr (b j * x) i) ≤ K)
    (P : ℤ[X][X]) (hE : P.natDegree ≤ E)
    (hP : ∀ j, length (P.coeff j) ≤ H) (i : Fin (d + 1)) :
    length (b.repr (aeval x P) i) ≤ (E + 1) * H * ((d + 1) * K) ^ E := by
  have hbase : 1 ≤ (d + 1 : ℝ) * K := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
  rw [repr_aeval]
  calc
    _ ≤ ∑ j ∈ Finset.range (P.natDegree + 1),
        length (P.coeff j * b.repr (x ^ j) i) := length_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (P.natDegree + 1), H * ((d + 1) * K) ^ E := by
      apply Finset.sum_le_sum
      intro j hj
      have hjE : j ≤ E := (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hE
      apply (length_mul_le _ _).trans
      exact mul_le_mul (hP j)
        ((power_length_bound b hb x K (by linarith) hM j i).trans
          (pow_le_pow_right₀ hbase hjE)) (length_nonneg _) hH
    _ ≤ (E + 1) * H * ((d + 1) * K) ^ E := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hE 1) hH)
        (by positivity)

end TranscendenceTheory.IntegralCoordinates

open Polynomial Module
open scoped Polynomial

namespace TranscendenceTheory.IntegralCoordinates

lemma exists_integral_power_basis (θ ν : ℂ) (hθ : Transcendental ℤ θ)
    (hν : ∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (aeval θ).toRingHom ν = 0) :
    ∃ (S : Subring ℂ) (hθS : θ ∈ S),
      letI : Algebra ℤ[X] S := (aeval (⟨θ, hθS⟩ : S)).toAlgebra
      ∃ (d : ℕ) (b : Basis (Fin (d + 1)) ℤ[X] S), b 0 = 1 ∧ ν ∈ S := by
  let : Algebra ℤ[X] ℂ := (aeval θ).toAlgebra
  have : IsTorsionFree ℤ[X] ℂ := (isTorsionFree_iff_algebraMap_injective).mpr
    ((transcendental_iff_injective.mp hθ))
  have hν' : IsIntegral ℤ[X] ν := hν
  let T := Algebra.adjoin ℤ[X] ({ν} : Set ℂ)
  let B := Algebra.adjoin.powerBasis' hν'
  have hθT : θ ∈ T := by
    have h := T.algebraMap_mem (X : ℤ[X])
    change aeval θ X ∈ T at h
    simpa only [aeval_X] using h
  have hAlg : (aeval (⟨θ, hθT⟩ : T)).toAlgebra = (inferInstance : Algebra ℤ[X] T) := by
    apply Algebra.algebra_ext
    intro p
    apply Subtype.ext
    change (aeval (⟨θ, hθT⟩ : T) p : ℂ) = aeval θ p
    simpa using (aeval_algHom_apply T.val.toIntAlgHom (⟨θ, hθT⟩ : T) p).symm
  refine ⟨T.toSubring, hθT, ?_⟩
  rw [hAlg]
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt B.dim_pos)
  let e : Fin B.dim ≃ Fin (d + 1) := finCongr hd
  refine ⟨d, B.basis.reindex e, ?_, Algebra.subset_adjoin (Set.mem_singleton ν)⟩
  rw [Basis.reindex_apply, B.basis_eq_pow]
  have he : (e.symm 0).val = 0 := rfl
  rw [he, pow_zero]

end TranscendenceTheory.IntegralCoordinates

open Polynomial Module
open scoped Polynomial

namespace TranscendenceTheory.IntegralCoordinates

open IntegralNorm

lemma finite_nat_bound {ι : Type*} [Finite ι] (f : ι → ℝ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ i, f i ≤ K := by
  obtain ⟨a, ha⟩ := (Set.finite_range f).bddAbove
  obtain ⟨K, hK⟩ := exists_nat_gt (max a 1)
  refine ⟨K, by exact_mod_cast (le_max_right a 1).trans hK.le, fun i ↦ ?_⟩
  exact (ha (Set.mem_range_self i)).trans ((le_max_left a 1).trans hK.le)

variable {S : Type*} [CommRing S] [Algebra ℤ[X] S]

lemma exists_coordinate_envelope {d : ℕ} (b : Basis (Fin (d + 1)) ℤ[X] S)
    (hb : b 0 = 1) (x : S) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ P : ℤ[X][X],
      (P.natDegree : ℝ) ≤ A * N →
      (∀ j, ((P.coeff j).natDegree : ℝ) ≤ A * N) →
      (∀ j k, |((P.coeff j).coeff k : ℝ)| ≤ Real.exp (A * N)) →
      (∀ i, ((b.repr (aeval x P) i).natDegree : ℝ) ≤ C * N) ∧
      (∀ i k, |((b.repr (aeval x P) i).coeff k : ℝ)| ≤ Real.exp (C * N)) := by
  classical
  obtain ⟨K, hK, hKM⟩ := finite_nat_bound
    (fun t : Fin (d + 1) × Fin (d + 1) ↦
      ((b.repr (b t.2 * x) t.1).natDegree : ℝ) + length (b.repr (b t.2 * x) t.1))
  have hKd : ∀ i j, (b.repr (b j * x) i).natDegree ≤ K := by
    intro i j
    have h := hKM (i, j)
    have hd : ((b.repr (b j * x) i).natDegree : ℝ) ≤ K := by
      linarith [length_nonneg (b.repr (b j * x) i)]
    exact_mod_cast hd
  have hKl : ∀ i j, length (b.repr (b j * x) i) ≤ K := by
    intro i j
    have h := hKM (i, j)
    have hd : (0 : ℝ) ≤ (b.repr (b j * x) i).natDegree := by positivity
    linarith
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  let B : ℝ := (d + 1) * K
  have hB : 1 ≤ B := by dsimp [B]; nlinarith [Nat.cast_nonneg (α := ℝ) d]
  let C : ℝ := (K + B + 4) * A
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N P hE hD hH
  let E := ⌊A * N⌋₊
  have hE' : P.natDegree ≤ E := Nat.le_floor hE
  have hD' : ∀ j, (P.coeff j).natDegree ≤ E := fun j ↦ Nat.le_floor (hD j)
  have hEr : (E : ℝ) ≤ A * N := Nat.floor_le (by positivity)
  have hEexp : (E + 1 : ℝ) ≤ Real.exp (A * N) := by
    linarith [Real.add_one_le_exp (A * N)]
  have hP : ∀ j, length (P.coeff j) ≤ (E + 1) * Real.exp (A * N) := by
    intro j
    apply (length_le_of_coeff_le _ _ (fun k ↦ by simpa [Int.norm_eq_abs] using hH j k)).trans
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.add_le_add_right (hD' j) 1) (Real.exp_pos _).le
  have hBpow : B ^ E ≤ Real.exp (B * A * N) := by
    calc
      _ ≤ (Real.exp B) ^ E := pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp B]) E
      _ = Real.exp (B * E) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hEr (by linarith : 0 ≤ B)])
  constructor
  · intro i
    have hdeg := eval_degree_bound b hb x K E E hKd P hE' hD' i
    calc
      _ ≤ (E : ℝ) + K * E := by exact_mod_cast hdeg
      _ ≤ (K + 1 : ℝ) * (A * N) := by
        nlinarith [mul_le_mul_of_nonneg_left hEr (by positivity : 0 ≤ (K : ℝ))]
      _ ≤ C * N := by dsimp [C]; nlinarith [mul_nonneg (by linarith : 0 ≤ B + 3) (by positivity : 0 ≤ A * N)]
  · intro i k
    have hlen := eval_length_bound b hb x (K : ℝ) ((E + 1) * Real.exp (A * N)) E
      hKr (by positivity) hKl P hE' hP i
    have hcoeff : |((b.repr (aeval x P) i).coeff k : ℝ)| ≤ length (b.repr (aeval x P) i) := by
      simpa [Int.norm_eq_abs] using norm_coeff_le_length (b.repr (aeval x P) i) k
    apply hcoeff.trans (hlen.trans ?_)
    change (E + 1 : ℝ) * ((E + 1) * Real.exp (A * N)) * B ^ E ≤ Real.exp (C * N)
    calc
      _ ≤ Real.exp (A * N) * (Real.exp (A * N) * Real.exp (A * N)) * Real.exp (B * A * N) := by
        exact mul_le_mul
          (mul_le_mul hEexp (mul_le_mul_of_nonneg_right hEexp (Real.exp_pos _).le)
            (by positivity) (Real.exp_pos _).le) hBpow (by positivity) (by positivity)
      _ = Real.exp ((B + 3) * A * N) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [C]; nlinarith [mul_nonneg (by positivity : 0 ≤ (K : ℝ) + 1) (by positivity : 0 ≤ A * N)])

end TranscendenceTheory.IntegralCoordinates

open Polynomial Module Filter
open scoped Polynomial

namespace TranscendenceTheory.IntegralCoordinates

theorem small_integral_coordinates_of_bivariate_values
    (θ ν : ℂ) (hθ : Transcendental ℤ θ)
    (hν : ∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (aeval θ).toRingHom ν = 0)
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c)
    (hsmall : ∀ᶠ N : ℕ in atTop, ∃ P : ℤ[X][X],
      (P.natDegree : ℝ) ≤ A * N ∧
      (∀ j, ((P.coeff j).natDegree : ℝ) ≤ A * N) ∧
      (∀ j k, |((P.coeff j).coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
      P.eval₂ (aeval θ).toRingHom ν ≠ 0 ∧
      ‖P.eval₂ (aeval θ).toRingHom ν‖ ≤ Real.exp (-c * (N : ℝ) ^ 2 * Real.log N)) :
    ∃ (S : Subring ℂ) (hθS : θ ∈ S) (d : ℕ),
      letI : Algebra ℤ[X] S := (aeval (⟨θ, hθS⟩ : S)).toAlgebra
      ∃ b : Basis (Fin (d + 1)) ℤ[X] S, b 0 = 1 ∧
        ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
          ∀ᶠ N : ℕ in atTop, ∃ x : S, x ≠ 0 ∧
            (∀ i, ((b.repr x i).natDegree : ℝ) ≤ C * N) ∧
            (∀ i k, |((b.repr x i).coeff k : ℝ)| ≤ Real.exp (C * N)) ∧
            ‖(x : ℂ)‖ ≤ Real.exp (-c * (N : ℝ) ^ 2 * Real.log N) := by
  obtain ⟨S, hθS, d, b, hb, hνS⟩ := exists_integral_power_basis θ ν hθ hν
  let : Algebra ℤ[X] S := (aeval (⟨θ, hθS⟩ : S)).toAlgebra
  let x : S := ⟨ν, hνS⟩
  obtain ⟨C, hC, henv⟩ := exists_coordinate_envelope b hb x A hA
  have hmap : S.subtype.comp (algebraMap ℤ[X] S) = (aeval θ).toRingHom := by
    apply RingHom.ext
    intro p
    change (aeval (⟨θ, hθS⟩ : S) p : ℂ) = aeval θ p
    simpa using (aeval_algHom_apply S.subtype.toIntAlgHom (⟨θ, hθS⟩ : S) p).symm
  have heval (P : ℤ[X][X]) : (aeval x P : ℂ) = P.eval₂ (aeval θ).toRingHom ν := by
    change S.subtype (P.eval₂ (algebraMap ℤ[X] S) x) = _
    rw [hom_eval₂, hmap]
    rfl
  refine ⟨S, hθS, d, b, hb, C, c, hC, hc, ?_⟩
  filter_upwards [hsmall] with N hN
  obtain ⟨P, hE, hD, hH, hP0, hPsmall⟩ := hN
  obtain ⟨hdeg, hheight⟩ := henv N P hE hD hH
  refine ⟨aeval x P, ?_, hdeg, hheight, ?_⟩
  · intro h
    apply hP0
    rw [← heval P, h]
    rfl
  · simpa only [heval] using hPsmall

end TranscendenceTheory.IntegralCoordinates

theorem solution
    (θ ν : ℂ) (hθ : Transcendental ℤ θ)
    (hν : ∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (aeval θ).toRingHom ν = 0)
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c)
    (hsmall : ∀ᶠ N : ℕ in atTop, ∃ P : ℤ[X][X],
      (P.natDegree : ℝ) ≤ A * N ∧
      (∀ j, ((P.coeff j).natDegree : ℝ) ≤ A * N) ∧
      (∀ j k, |((P.coeff j).coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
      P.eval₂ (aeval θ).toRingHom ν ≠ 0 ∧
      ‖P.eval₂ (aeval θ).toRingHom ν‖ ≤ Real.exp (-c * (N : ℝ) ^ 2 * Real.log N)) :
    ∃ (S : Subring ℂ) (hθS : θ ∈ S) (d : ℕ),
      letI : Algebra ℤ[X] S := (aeval (⟨θ, hθS⟩ : S)).toAlgebra
      ∃ b : Basis (Fin (d + 1)) ℤ[X] S, b 0 = 1 ∧
        ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
          ∀ᶠ N : ℕ in atTop, ∃ x : S, x ≠ 0 ∧
            (∀ i, ((b.repr x i).natDegree : ℝ) ≤ C * N) ∧
            (∀ i k, |((b.repr x i).coeff k : ℝ)| ≤ Real.exp (C * N)) ∧
            ‖(x : ℂ)‖ ≤ Real.exp (-c * (N : ℝ) ^ 2 * Real.log N) := by
  exact TranscendenceTheory.IntegralCoordinates.small_integral_coordinates_of_bivariate_values
    θ ν hθ hν A c hA hc hsmall

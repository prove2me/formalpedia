-- Prove2me | solution 1 for ShapleySnowSG.Kernel.lemma_C2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T21:26:44.480193+00:00
-- url     : https://prove2.me/submissions/1bffa09d-12c5-455b-86b9-867b32c8fede

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_KroneckerMEP

open Matrix Polynomial

namespace SSKAux
open ShapleySnowSG.Kernel

lemma det_rows_sum {K : Type*} [Field K] {n : ℕ} {q : Fin n → Type*} [∀ k, Fintype (q k)]
    (F : ∀ k : Fin n, q k → Fin n → K) (y : ∀ k, q k → K) :
    ∑ j : (∀ k, q k), (Matrix.of fun k m => F k (j k) m).det * ∏ k, y k (j k)
      = (Matrix.of fun k m => ∑ b, F k b m * y k b).det := by
  have h1 : (Matrix.of fun k m => ∑ b, F k b m * y k b) = fun k => ∑ b, y k b • F k b := by
    ext k m; simp [Finset.sum_apply, mul_comm]
  rw [h1]
  have := (Matrix.detRowAlternating (n := Fin n) (R := K)).toMultilinearMap.map_sum
    (fun k b => y k b • F k b)
  change _ = (Matrix.detRowAlternating (n := Fin n) (R := K)).toMultilinearMap _
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]
  rfl

lemma aux_mulVec_tensor {K : Type*} [Field K] {n : ℕ} {p q : Fin n → Type*}
    [∀ k, Fintype (q k)]
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (q k) K) (y : ∀ k, q k → K)
    (ℓ : Fin (n + 1)) (i : ∀ k, p k) :
    (aux M ℓ *ᵥ tensorVec y) i =
      (-1) ^ (ℓ : ℕ) * (Matrix.of fun k m => (M k (ℓ.succAbove m) *ᵥ y k) (i k)).det := by
  simp only [mulVec, dotProduct, aux, kronDet, tensorVec, Matrix.smul_apply, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  exact det_rows_sum (fun k b m => M k (ℓ.succAbove m) (i k) b) y

lemma kron_kernel {K : Type*} [Field K] {n : ℕ} {p q : Fin n → Type*}
    [∀ k, Fintype (q k)]
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (q k) K) (z : Fin n → K) (y : ∀ k, q k → K)
    (hy : ∀ k, pencil M z k *ᵥ y k = 0) (k : Fin n) :
    (aux M k.succ - z k • aux M 0) *ᵥ tensorVec y = 0 := by
  funext i
  set a : Matrix (Fin n) (Fin (n + 1)) K := Matrix.of fun k' l => (M k' l *ᵥ y k') (i k') with ha_def
  let u : Fin (n + 1) → K := Fin.cons 1 z
  have ha : ∀ k', ∑ l, a k' l * u l = 0 := by
    intro k'
    have := congrFun (hy k') (i k')
    rw [Fin.sum_univ_succ]
    simp only [pencil, add_mulVec, Matrix.sum_mulVec, smul_mulVec, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [ha_def, u, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, mul_one]
    rw [← this]
    congr 1
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  let e : Fin (n + 1) → K := fun j => (if j = k.succ then 1 else 0) - z k * (if j = 0 then 1 else 0)
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of (Fin.cons e (fun k' => a k'))
  have hB : B.det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨u, ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp [u] at this
    · funext j
      refine Fin.cases ?_ (fun k' => ?_) j
      · simp only [mulVec, dotProduct, B, Matrix.of_apply, Fin.cons_zero, e, Pi.zero_apply]
        rw [Fin.sum_univ_succ]
        simp [u, Fin.succ_ne_zero, Finset.sum_ite_eq', Fin.succ_inj, (Fin.succ_ne_zero k).symm]
      · simp only [mulVec, dotProduct, B, Matrix.of_apply, Fin.cons_succ, Pi.zero_apply]
        exact ha k'
  rw [det_succ_row_zero] at hB
  simp only [B, Matrix.of_apply, Fin.cons_zero, e, Matrix.submatrix, Fin.cons_succ] at hB
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hB
  rw [sub_mulVec, Pi.sub_apply, smul_mulVec, Pi.smul_apply, smul_eq_mul,
    aux_mulVec_tensor, aux_mulVec_tensor, Pi.zero_apply]
  rw [← hB]
  simp only [Fin.val_zero, pow_zero, one_mul, a]
  rfl

lemma tensorVec_ne_zero {K : Type*} [Field K] {n : ℕ} {q : Fin n → Type*}
    (y : ∀ k, q k → K) (hy0 : ∀ k, y k ≠ 0) : tensorVec y ≠ 0 := by
  have : ∀ k, ∃ b, y k b ≠ 0 := fun k => by
    by_contra h
    push Not at h
    exact hy0 k (funext h)
  choose b hb using this
  intro h
  have := congrFun h b
  simp only [tensorVec, Pi.zero_apply] at this
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => hb k) this

end SSKAux

open ShapleySnowSG.Kernel in
theorem solution {n : ℕ} {p : Fin n → Type*} [∀ k, Fintype (p k)] [∀ k, DecidableEq (p k)]
    (M : ∀ k : Fin n, Fin (n + 1) → Matrix (p k) (p k) ℝ)
    (z : Fin n → ℂ) (_hz : z ∈ SM (complexArray M))
    (y : ∀ k, p k → ℂ) (hy0 : ∀ k, y k ≠ 0)
    (hy : ∀ k, pencil (complexArray M) z k *ᵥ y k = 0) :
    z ∈ SDelta (complexArray M) ∧ ∀ k,
      (aux (complexArray M) k.succ - z k • aux (complexArray M) 0) *ᵥ tensorVec y = 0 := by
  have hker := fun k => SSKAux.kron_kernel (complexArray M) z y hy k
  refine ⟨fun k => ?_, hker⟩
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨tensorVec y, SSKAux.tensorVec_ne_zero y hy0, hker k⟩

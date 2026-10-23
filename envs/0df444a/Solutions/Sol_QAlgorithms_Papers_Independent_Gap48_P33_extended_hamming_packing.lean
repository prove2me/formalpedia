-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P33.extended_hamming_packing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:36:18.117713+00:00
-- url     : https://prove2.me/submissions/aede8331-65f4-4a24-b4c0-f3b99d084df5

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33

namespace X6Ham
open Polynomial

theorem gen (n : ℕ) :
    (∑ e : Fin n → Fin 4, (X : ℕ[X]) ^ (Finset.univ.filter fun i => e i ≠ 0).card) =
      (1 + C 3 * X) ^ n := by
  have h1 : ∀ e : Fin n → Fin 4, (X : ℕ[X]) ^ (Finset.univ.filter fun i => e i ≠ 0).card =
      ∏ i, (if e i ≠ 0 then X else 1) := by
    intro e
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (j : Fin 4) => if j ≠ 0 then (X : ℕ[X]) else 1)]
  simp [Fin.sum_univ_four]
  ring

theorem count (n i : ℕ) :
    (Finset.univ.filter fun e : Fin n → Fin 4 =>
      (Finset.univ.filter fun j => e j ≠ 0).card = i).card = 3 ^ i * n.choose i := by
  have h := congrArg (fun p => Polynomial.coeff p i) (gen n)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow] at h
  rw [Finset.card_filter]
  convert h using 1
  · exact Finset.sum_congr rfl fun e _ => if_congr eq_comm rfl rfl
  · rw [add_comm, add_pow]
    simp only [one_pow, mul_one, Polynomial.finsetSum_coeff, mul_pow, ← Polynomial.C_pow]
    have hb : ∀ b, (C (3 ^ b) * X ^ b * ((n.choose b : ℕ) : ℕ[X])).coeff i =
        if i = b then 3 ^ b * n.choose b else 0 := by
      intro b
      rw [show ((n.choose b : ℕ) : ℕ[X]) = C (n.choose b) from (Polynomial.C_eq_natCast _).symm,
        mul_comm, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow, mul_comm]
    simp_rw [hb]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · simp at h
      rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]

end X6Ham

namespace X6P33
open QAlgorithms.Papers.Independent.Gap48.P33
open QAlgorithms.Papers.Independent.Claimed50.P03 (pauliWeight wordSupport)

noncomputable instance errFin (n t : ℕ) : Fintype (ErrorWords n t) := by
  unfold ErrorWords; infer_instance

theorem card_err (n t : ℕ) : Fintype.card (ErrorWords n t) = ballVolume 3 n t := by
  classical
  have h1 : Fintype.card (ErrorWords n t) =
      (Finset.univ.filter fun e : Fin n → Fin 4 => pauliWeight e ≤ t).card := by
    convert Fintype.card_subtype (fun e : Fin n → Fin 4 => pauliWeight e ≤ t); rfl
  rw [h1, ballVolume]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun e : Fin n → Fin 4 => pauliWeight e)
    (t := Finset.range (t + 1)) (fun e he => by simp at he ⊢; omega)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.filter_filter, ← X6Ham.count n i]
  congr 1
  ext e
  simp at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change _ ∧ _ ↔ pauliWeight e = i
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by omega, h⟩

theorem packing (n k t : ℕ) (hcode : ExtendedCode n k t) :
    2 ^ k * ballVolume 3 n t ≤ 2 ^ (2 * n) := by
  obtain ⟨v, hv⟩ := hcode
  have := hv.linearIndependent.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, card_err, finrank_euclideanSpace,
    Fintype.card_prod] at this
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
  exact this.trans (le_of_eq (by ring))

end X6P33

open QAlgorithms.Papers.Independent.Gap48.P33 in
theorem solution (n k t : ℕ) (ht : t ≤ n)
    (hcode : ExtendedCode n k t) :
    2 ^ k * ballVolume 3 n t ≤ 2 ^ (2 * n) := X6P33.packing n k t hcode

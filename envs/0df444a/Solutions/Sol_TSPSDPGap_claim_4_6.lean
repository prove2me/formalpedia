-- Prove2me | solution 1 for TSPSDPGap.claim_4_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:46:30.270476+00:00
-- url     : https://prove2.me/submissions/0665dc7d-71fd-446a-a3e0-77a4bb70c2b4

import Mathlib
import Definitions.Def_TSPSDPGap_Ymat
open scoped Kronecker

namespace Aux_TSP46

open TSPSDPGap

theorem cb_diag (n i : ℕ) (hi1 : 1 ≤ i) (hi2 : i < n) (b : Fin n) : circBasis n i b b = 0 := by
  simp only [circBasis, Matrix.of_apply]
  have h1 : ((b : ℕ) + n - b) % n = 0 := by rw [Nat.add_sub_cancel_left, Nat.mod_self]
  have h2 : i % n = i := Nat.mod_eq_of_lt hi2
  rw [h1, h2, if_neg (by omega)]
  norm_num

theorem A_diag (g n : ℕ) (hn : 0 < n) (b : Fin n) : Amat g n b b = 0 := by
  simp only [Amat, Matrix.sum_apply, Matrix.smul_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [cb_diag n i hi.1 (by omega) b, smul_zero]

theorem B_diag (g n : ℕ) (hn : 0 < n) (b : Fin n) : Bmat g n b b = 0 := by
  simp only [Bmat, Matrix.sum_apply, Matrix.smul_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [cb_diag n i hi.1 (by omega) b, smul_zero]

end Aux_TSP46

open TSPSDPGap Aux_TSP46 in
theorem solution (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    Matrix.trace (((1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ (Matrix.of (fun _ _ => (1 : ℝ)) - 1) +
      (Matrix.of (fun _ _ => (1 : ℝ)) - 1) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)) * Ymat g n) = 0 := by
  have hn : 0 < n := by omega
  have hA := A_diag g n hn
  have hB := B_diag g n hn
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro x _
  rw [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro y _
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2
  · simp [Matrix.kroneckerMap_apply, Matrix.one_apply, h1, h2]
  · have h2' : y.2 ≠ x.2 := fun h => h2 h.symm
    simp [Ymat, h1, h2']
  · have h1' : y.1 ≠ x.1 := fun h => h1 h.symm
    simp [Ymat, h1', h2, hA, hB]
  · simp [Matrix.kroneckerMap_apply, Matrix.one_apply, h1, h2]

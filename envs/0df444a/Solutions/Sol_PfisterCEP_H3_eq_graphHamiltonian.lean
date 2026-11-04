-- Prove2me | solution 1 for PfisterCEP.H3_eq_graphHamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-03T19:55:49.311081+00:00
-- url     : https://prove2.me/submissions/356ae53f-3364-4060-824e-7c48d485196d

import Mathlib
import Definitions.Def_PfisterCEP_IsCCR
import Definitions.Def_PfisterCEP_graphHamiltonian
import Definitions.Def_PfisterCEP_H3

namespace PfisterCEP

private theorem symmetric_pair_sum {ι M : Type*} [LinearOrder ι] [Fintype ι]
    [AddCommMonoid M] (f : ι → ι → M) (hsym : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) =
      (∑ i, ∑ j ∈ Finset.univ.filter (i < ·), f i j) +
      (∑ i, ∑ j ∈ Finset.univ.filter (i < ·), f i j) +
      ∑ i, f i i := by
  classical
  have hpoint (i j : ι) : f i j =
      (if i < j then f i j else 0) +
      (if j < i then f i j else 0) +
      (if i = j then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, (lt_asymm h), (ne_of_lt h)]
    · subst j; simp
    · simp [h, (lt_asymm h), (ne_of_gt h)]
  have hswap : (∑ i, ∑ j ∈ Finset.univ.filter (· < i), f i j) =
      (∑ i, ∑ j ∈ Finset.univ.filter (i < ·), f i j) := by
    calc
      _ = ∑ i, ∑ j, if j < i then f i j else 0 := by simp [Finset.sum_ite]
      _ = ∑ j, ∑ i, if j < i then f i j else 0 := Finset.sum_comm
      _ = ∑ j, ∑ i, if j < i then f j i else 0 := by simp_rw [hsym]
      _ = _ := by simp [Finset.sum_ite]
  calc
    (∑ i, ∑ j, f i j) =
        ∑ i, ∑ j, ((if i < j then f i j else 0) +
          (if j < i then f i j else 0) +
          (if i = j then f i j else 0)) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            exact hpoint i j
    _ = (∑ i, ∑ j ∈ Finset.univ.filter (i < ·), f i j) +
        (∑ i, ∑ j ∈ Finset.univ.filter (· < i), f i j) + ∑ i, f i i := by
          simp [Finset.sum_add_distrib, Finset.sum_ite]
    _ = _ := by rw [hswap]

private theorem half_pair_smul {A : Type*} [Ring A] [Algebra ℂ A]
    (c : ℂ) (P D : A) : (c / 2) • (P + P + D) = c • (P + (1 / 2 : ℂ) • D) := by
  simp only [smul_add, smul_smul]
  have hc : c / 2 + c / 2 = c := by ring
  rw [← add_smul, hc]
  congr 1
  module

end PfisterCEP

open PfisterCEP

theorem solution {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ}
    (a ad : Fin N → A) (hccr : IsCCR a ad) (ħ κ : ℝ) :
    H3 ħ κ a ad =
      graphHamiltonian ħ κ (Matrix.of fun _ _ => (1 : ℝ)) a ad := by
  classical
  have had := PfisterCEP.symmetric_pair_sum (fun n p : Fin N => ad n * ad p) hccr.2.2
  have ha := PfisterCEP.symmetric_pair_sum (fun n p : Fin N => a p * a n)
    (fun i j => hccr.2.1 j i)
  simp only [H3, graphHamiltonian, Matrix.of_apply, Complex.ofReal_one, one_smul]
  rw [had, ha]
  simp only [← Finset.smul_sum]
  rw [← neg_div]
  -- Both halves follow from the same scalar identity.
  congr 1
  · exact (PfisterCEP.half_pair_smul (A := A) (Complex.I * ħ * κ) _ _).symm
  · exact (PfisterCEP.half_pair_smul (A := A) (-(Complex.I * ħ * κ)) _ _).symm

-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ArtinSchreier.frobeniusCombo_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:42:55.567515+00:00
-- url     : https://prove2.me/submissions/148f4532-fc1e-4eeb-ad69-b82b1638bbe7

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreier
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ArtinSchreier_val_of_frobenius_fixed
section
namespace QEC.Coding.AlgebraicGeometry.ArtinSchreier
open scoped WithZero BigOperators
open Polynomial
variable {F : Type*} [Field F]
private theorem exp_lt_exp {a b : ℤ} : WithZero.exp a < WithZero.exp b ↔ a < b := by
  simp [WithZero.exp]
end QEC.Coding.AlgebraicGeometry.ArtinSchreier
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ArtinSchreier
open scoped WithZero BigOperators
open Polynomial
variable {F : Type*} [Field F]
namespace QEC.Coding.AlgebraicGeometry.ArtinSchreier
theorem _root_.solution (ν : Valuation F ℤᵐ⁰) (u : F)
    (hu : ν u = WithZero.exp (33 : ℤ)) {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (a : F) (c : Fin (m + 1) → F) (hc : ∀ j : Fin (m + 1), c j ^ 32 = c j)
    (hcTop : c ⟨m, Nat.lt_succ_self m⟩ = 1) :
    u ≠ ∑ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ)) := by
  intro h
  have hν : ν (∑ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ))) = WithZero.exp (33 : ℤ) := by
    rw [← h, hu]
  by_cases ha0 : a = 0
  · -- a = 0 makes the whole sum vanish, contradicting `ν u = exp 33 ≠ 0`
    subst a
    have hsum : (∑ j : Fin (m + 1), c j * 0 ^ (2 ^ (j : ℕ))) = 0 := by
      simp
    have hu0 : u = 0 := by simpa [hsum] using h
    rw [hu0, Valuation.map_zero] at hu
    exact WithZero.exp_ne_zero hu.symm
  · -- ν a = exp r, r : ℤ
    have hva0 : ν a ≠ 0 := (Valuation.ne_zero_iff ν).mpr ha0
    let r : ℤ := WithZero.log (ν a)
    have hae : ν a = WithZero.exp r := by
      dsimp [r]
      exact (WithZero.exp_log hva0).symm
    have hcv : ∀ j : Fin (m + 1), ν (c j) = 0 ∨ ν (c j) = 1 :=
      fun j => val_of_frobenius_fixed ν (hc j)
    have hg : ∀ j : Fin (m + 1),
        ν (c j * a ^ (2 ^ (j : ℕ))) = ν (c j) * WithZero.exp (((2 ^ (j : ℕ) : ℕ) : ℤ) * r) := by
      intro j
      rw [map_mul, map_pow, hae, ← WithZero.exp_nsmul, nsmul_eq_mul]
    by_cases hrpos : 0 < r
    · -- r > 0: the top term `a^{2^m}` (coefficient 1) strictly dominates
      let g : Fin (m + 1) → ℤᵐ⁰ := fun j => ν (c j * a ^ (2 ^ (j : ℕ)))
      let jmax : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
      have hgmax : g jmax = WithZero.exp (((2 ^ m : ℕ) : ℤ) * r) := by
        dsimp [g, jmax]
        rw [hg, hcTop, ν.map_one, one_mul]
        norm_cast
      have hstrict : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))) \ {jmax}, g i < g jmax := by
        intro i hi
        have hine : i ≠ jmax := by
          simpa using (Finset.mem_sdiff.mp hi).2
        have him : (i : ℕ) < m := by
          have hilt : (i : ℕ) < m + 1 := i.isLt
          have hineN : (i : ℕ) ≠ m := by
            intro hiN
            exact hine (Fin.ext hiN)
          omega
        have hpowlt : (2 ^ (i : ℕ) : ℕ) < 2 ^ m := by
          exact pow_lt_pow_right₀ (by norm_num : (1 : ℕ) < 2) him
        have hpowltz : ((2 ^ (i : ℕ) : ℕ) : ℤ) < ((2 ^ m : ℕ) : ℤ) := by
          exact_mod_cast hpowlt
        have hci : ν (c i) ≤ 1 := by
          rcases hcv i with h0 | h1
          · exact le_trans (le_of_eq h0) (zero_le (a := (1 : ℤᵐ⁰)))
          · exact le_of_eq h1
        have hgile : g i ≤ WithZero.exp (((2 ^ (i : ℕ) : ℕ) : ℤ) * r) := by
          dsimp [g]
          rw [hg]
          simpa using mul_le_mul_left hci (WithZero.exp (((2 ^ (i : ℕ) : ℕ) : ℤ) * r))
        have hexp : WithZero.exp (((2 ^ (i : ℕ) : ℕ) : ℤ) * r) <
            WithZero.exp (((2 ^ m : ℕ) : ℤ) * r) := by
          rw [exp_lt_exp]
          exact mul_lt_mul_of_pos_right hpowltz hrpos
        exact lt_of_le_of_lt hgile (hexp.trans_eq hgmax.symm)
      have hsum : ν (∑ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ))) = g jmax := by
        change ν (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))),
          (fun i : Fin (m + 1) => c i * a ^ (2 ^ (i : ℕ))) i) = ν
          ((fun i : Fin (m + 1) => c i * a ^ (2 ^ (i : ℕ))) jmax)
        exact ν.map_sum_eq_of_lt (Finset.mem_univ jmax) (by intro i hi; exact hstrict i hi)
      rw [hsum, hgmax] at hν
      have hEq : ((2 ^ m : ℕ) : ℤ) * r = 33 := WithZero.exp_inj.mp hν
      interval_cases m <;> norm_num at hEq <;> omega
    · by_cases hrneg : r < 0
      · -- r < 0: the strict maximum over the finitely many term valuations is
        -- attained at a unique index, and equals `exp (2^{j₀}·r)`
        let g : Fin (m + 1) → ℤᵐ⁰ := fun j => ν (c j * a ^ (2 ^ (j : ℕ)))
        obtain ⟨jmax, hjmem, hjmaxle⟩ :=
          Finset.exists_max_image (Finset.univ : Finset (Fin (m + 1))) g
            (Finset.univ_nonempty)
        have hsum0 : (∑ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ))) ≠ 0 := by
          intro hs
          have hz : ν (∑ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ))) = 0 := by
            simp [hs]
          rw [hν] at hz
          exact WithZero.exp_ne_zero hz
        have hex : ∃ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ)) ≠ 0 := by
          by_contra hne
          have hne' : ∀ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ)) = 0 := by
            intro j
            by_contra hj
            exact hne ⟨j, hj⟩
          exact hsum0 (Finset.sum_eq_zero (fun j _ => hne' j))
        rcases hex with ⟨j0, hj0⟩
        have hgmax0 : g jmax ≠ 0 := by
          intro hz
          have hle : g j0 ≤ g jmax := hjmaxle j0 (Finset.mem_univ j0)
          have hg0 : g j0 ≠ 0 := by
            dsimp [g]
            exact (Valuation.ne_zero_iff ν).mpr hj0
          rw [hz] at hle
          exact hg0 (le_antisymm hle (zero_le (a := g j0)))
        have hstrict : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))) \ {jmax}, g i < g jmax := by
          intro i hi
          have hle : g i ≤ g jmax := hjmaxle i (Finset.mem_univ i)
          have hne : g i ≠ g jmax := by
            intro hEq
            have hine : i ≠ jmax := by simpa using (Finset.mem_sdiff.mp hi).2
            have hci : c i ≠ 0 := by
              intro hcz
              have : g i = 0 := by dsimp [g]; simp [hcz]
              exact hgmax0 (hEq.symm.trans this)
            have hνci : ν (c i) = 1 := by
              rcases hcv i with h0 | h1
              · exfalso; exact hci ((Valuation.zero_iff ν).mp h0)
              · exact h1
            have gi : g i = WithZero.exp (((2 ^ (i : ℕ) : ℕ) : ℤ) * r) := by
              dsimp [g]
              rw [hg, hνci, one_mul]
              norm_cast
            have hcj : c jmax ≠ 0 := by
              intro hcz
              have : g jmax = 0 := by dsimp [g]; simp [hcz]
              exact hgmax0 this
            have hνcj : ν (c jmax) = 1 := by
              rcases hcv jmax with h0 | h1
              · exfalso; exact hcj ((Valuation.zero_iff ν).mp h0)
              · exact h1
            have gj : g jmax = WithZero.exp (((2 ^ (jmax : ℕ) : ℕ) : ℤ) * r) := by
              dsimp [g]
              rw [hg, hνcj, one_mul]
              norm_cast
            have hexp : ((2 ^ (i : ℕ) : ℕ) : ℤ) * r = ((2 ^ (jmax : ℕ) : ℕ) : ℤ) * r := by
              rw [gi, gj] at hEq
              exact WithZero.exp_inj.mp hEq
            have hr0 : r ≠ 0 := ne_of_lt hrneg
            have hpow : ((2 ^ (i : ℕ) : ℕ) : ℤ) = ((2 ^ (jmax : ℕ) : ℕ) : ℤ) := by
              exact mul_right_cancel₀ hr0 hexp
            have hpowN : 2 ^ (i : ℕ) = 2 ^ (jmax : ℕ) := by exact_mod_cast hpow
            have hij : i = jmax := by
              apply Fin.ext
              exact (pow_right_injective₀ (by norm_num : (0 : ℕ) < 2) (by norm_num : (2 : ℕ) ≠ 1)) hpowN
            exact hine hij
          exact lt_of_le_of_ne hle hne
        have hsum : ν (∑ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ))) = g jmax := by
          change ν (∑ i ∈ (Finset.univ : Finset (Fin (m + 1))),
            (fun i : Fin (m + 1) => c i * a ^ (2 ^ (i : ℕ))) i) = ν
            ((fun i : Fin (m + 1) => c i * a ^ (2 ^ (i : ℕ))) jmax)
          exact ν.map_sum_eq_of_lt (Finset.mem_univ jmax) (by intro i hi; exact hstrict i hi)
        have hcj : c jmax ≠ 0 := by
          intro hcz
          have : g jmax = 0 := by dsimp [g]; simp [hcz]
          exact hgmax0 this
        have hνcj : ν (c jmax) = 1 := by
          rcases hcv jmax with h0 | h1
          · exfalso; exact hcj ((Valuation.zero_iff ν).mp h0)
          · exact h1
        have hgmaxexp : g jmax = WithZero.exp (((2 ^ (jmax : ℕ) : ℕ) : ℤ) * r) := by
          dsimp [g]
          rw [hg, hνcj, one_mul]
          norm_cast
        rw [hsum, hgmaxexp] at hν
        have hEq : ((2 ^ (jmax : ℕ) : ℕ) : ℤ) * r = 33 := WithZero.exp_inj.mp hν
        have hpos : (0 : ℤ) < ((2 ^ (jmax : ℕ) : ℕ) : ℤ) := by
          exact_mod_cast (pow_pos (by norm_num : (0 : ℕ) < 2) (jmax : ℕ))
        have hneg : ((2 ^ (jmax : ℕ) : ℕ) : ℤ) * r < 0 := mul_neg_of_pos_of_neg hpos hrneg
        omega -- (2^{j₀}·r = 33) and (2^{j₀}·r < 0)
      · -- r = 0: every term has valuation ≤ 1, but the sum has valuation exp 33 > 1
        have hr0 : r = 0 := by omega
        have hle1 : ∀ j : Fin (m + 1), ν (c j * a ^ (2 ^ (j : ℕ))) ≤ 1 := by
          intro j
          rcases hcv j with h0 | h1
          · rw [hg, h0]
            simp
          · rw [hg, h1, hr0]
            simp
        have hsumle : ν (∑ j : Fin (m + 1), c j * a ^ (2 ^ (j : ℕ))) ≤ 1 := by
          refine (Finset.sum_induction
            (fun j : Fin (m + 1) => c j * a ^ (2 ^ (j : ℕ))) (fun x : F => ν x ≤ 1)
            (fun x y hx hy => ν.map_add_le hx hy) (by simp) ?_)
          intro j
          simp only [Finset.mem_univ, true_implies]
          exact hle1 j
        have hlt1 : 1 < WithZero.exp (33 : ℤ) := exp_lt_exp.mpr (by norm_num)
        rw [hν] at hsumle
        exact (not_lt_of_ge hsumle) hlt1
end QEC.Coding.AlgebraicGeometry.ArtinSchreier

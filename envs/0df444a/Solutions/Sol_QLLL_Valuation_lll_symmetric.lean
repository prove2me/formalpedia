-- Prove2me | solution 1 for QLLL.Valuation.lll_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:48:10.410285+00:00
-- url     : https://prove2.me/submissions/fd2af201-d7c7-403d-907b-9c2b0c67de90

import Definitions.Def_QLLL_LocalLemma_Basic
import Theorems.Thm_QLLL_Valuation_lll
import Mathlib

section

open QLLL
open Finset
open QLLL.Valuation
variable {α : Type*} [Lattice α] [BoundedOrder α]
variable (R : Valuation α)
variable {n : ℕ} {X : Fin n → α} {Γ : Fin n → Finset (Fin n)} {y : Fin n → ℝ}

theorem solution {p : ℝ} {d : ℕ} (hΓ : R.IsDependencyGraph X Γ)
    (hd : ∀ i, (Γ i).card ≤ d) (hX : ∀ i, 1 - p ≤ R (X i))
    (hp : p * Real.exp 1 * (d + 1) ≤ 1) :
    0 < R (univ.inf X) := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd1
  · -- `d = 0`: every family is mutually independent, take `y i = max p 0`.
    subst hd0
    simp only [Nat.cast_zero, zero_add, mul_one] at hp
    have hΓ0 : ∀ i, Γ i = ∅ := fun i =>
      Finset.card_eq_zero.mp (Nat.le_zero.mp (hd i))
    have he2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    have hplt : p < 1 := by
      rcases le_total p 0 with h | h
      · linarith
      · nlinarith
    have hy₀ : ∀ _ : Fin n, (0:ℝ) ≤ max p 0 := fun _ => le_max_right _ _
    have hy₁ : ∀ _ : Fin n, max p 0 < 1 := fun _ => max_lt hplt one_pos
    have hXcond : ∀ i : Fin n,
        1 - max p 0 * ∏ j ∈ Γ i, (1 - max p 0) ≤ R (X i) := by
      intro i
      rw [hΓ0 i, Finset.prod_empty, mul_one]
      linarith [hX i, le_max_left p 0]
    have hres := lll (y := fun _ => max p 0) R hΓ hy₀ hy₁ hXcond
    have hprod : 0 < ∏ _i : Fin n, (1 - max p 0) :=
      Finset.prod_pos fun i _ => by linarith [hy₁ i]
    linarith
  · -- `d ≥ 1`: take `y i = 1/(d+1)` and use `(1 + 1/d) ^ d ≤ e`.
    have hD1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
    have hd1pos : (0:ℝ) < (d:ℝ) + 1 := by linarith
    have hexp1 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    set q : ℝ := 1 - 1/((d:ℝ)+1) with hqdef
    have hq0 : 0 < q := by
      rw [hqdef, sub_pos, div_lt_one hd1pos]; linarith
    have hq1 : q < 1 := by
      rw [hqdef, sub_lt_self_iff]; positivity
    have hstep : (1 + 1/(d:ℝ)) ^ d ≤ Real.exp 1 := by
      have h1 : 1 + 1/(d:ℝ) ≤ Real.exp (1/(d:ℝ)) := by
        linarith [Real.add_one_le_exp (1/(d:ℝ))]
      have h2 : (1 + 1/(d:ℝ)) ^ d ≤ (Real.exp (1/(d:ℝ))) ^ d :=
        pow_le_pow_left₀ (by positivity) h1 d
      have h3 : (Real.exp (1/(d:ℝ))) ^ d = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
      linarith [h2, h3.ge, h3.le]
    have hdpos : (0:ℝ) < (d:ℝ) := by linarith
    have hmul : q * (1 + 1/(d:ℝ)) = 1 := by
      rw [hqdef]
      field_simp
      ring
    have hqdpow : q ^ d * (1 + 1/(d:ℝ)) ^ d = 1 := by
      rw [← mul_pow, hmul, one_pow]
    have hqd : 1 ≤ Real.exp 1 * q ^ d := by
      have h := mul_le_mul_of_nonneg_right hstep (pow_nonneg hq0.le d)
      linarith [hqdpow]
    have hXcond : ∀ i : Fin n,
        1 - (1/((d:ℝ)+1)) * ∏ j ∈ Γ i, (1 - 1/((d:ℝ)+1)) ≤ R (X i) := by
      intro i
      have hprodq : (∏ _j ∈ Γ i, q) = q ^ (Γ i).card := Finset.prod_const q
      have hge : q ^ d ≤ q ^ (Γ i).card :=
        pow_le_pow_of_le_one hq0.le hq1.le (hd i)
      have hqk : 1 ≤ Real.exp 1 * q ^ (Γ i).card := by nlinarith
      have hple : p ≤ (1/((d:ℝ)+1)) * q ^ (Γ i).card := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hd1pos]
        nlinarith [pow_nonneg hq0.le (Γ i).card]
      rw [← hqdef, hprodq]
      linarith [hX i]
    have hy₀ : ∀ _ : Fin n, (0:ℝ) ≤ 1/((d:ℝ)+1) := fun _ => by positivity
    have hy₁ : ∀ _ : Fin n, (1:ℝ)/((d:ℝ)+1) < 1 := fun _ => by
      rw [div_lt_one hd1pos]; linarith
    have hres := lll (y := fun _ => 1/((d:ℝ)+1)) R hΓ hy₀ hy₁ hXcond
    have hprod : 0 < ∏ _i : Fin n, (1 - 1/((d:ℝ)+1)) :=
      Finset.prod_pos fun i _ => hq0
    linarith

end

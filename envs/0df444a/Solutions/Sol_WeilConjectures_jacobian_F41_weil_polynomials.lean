-- Prove2me | solution 1 for WeilConjectures.jacobian_F41_weil_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:48:02.095966+00:00
-- url     : https://prove2.me/submissions/8b8fca40-ced5-4b34-8c57-ce253bbaf2ad

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction

open Polynomial

namespace WEJ

noncomputable def Wf (s : Multiset ℂ) (i : ℕ) : ℂ[X] :=
  ((s.powersetCard i).map fun t => 1 - C t.prod * X).prod

lemma Wf_cons_zero (s : Multiset ℂ) (i : ℕ) : Wf (0 ::ₘ s) i = Wf s i := by
  cases i with
  | zero => simp [Wf, Multiset.powersetCard_zero_left]
  | succ i =>
    unfold Wf
    rw [Multiset.powersetCard_cons, Multiset.map_add, Multiset.prod_add, Multiset.map_map]
    have : ((Multiset.powersetCard i s).map ((fun t : Multiset ℂ => 1 - C t.prod * X) ∘
        Multiset.cons 0)).prod = 1 := by
      apply Multiset.prod_eq_one
      intro x hx
      simp only [Multiset.mem_map, Function.comp_apply, Multiset.prod_cons, zero_mul, map_zero,
        sub_zero] at hx
      obtain ⟨_, _, rfl⟩ := hx
      rfl
    rw [this, mul_one]

lemma Wf_replicate_zero (s : Multiset ℂ) (k i : ℕ) :
    Wf (Multiset.replicate k 0 + s) i = Wf s i := by
  induction k with
  | zero => simp
  | succ k ih => rw [Multiset.replicate_succ, Multiset.cons_add, Wf_cons_zero, ih]

lemma prod_cons_zero (s : Multiset ℂ) (k : ℕ) :
    ((Multiset.replicate k 0 + s).map fun a => 1 - C a * X).prod = (s.map fun a => 1 - C a * X).prod := by
  induction k with
  | zero => simp
  | succ k ih => rw [Multiset.replicate_succ, Multiset.cons_add, Multiset.map_cons,
      Multiset.prod_cons, ih]; simp

lemma split (α : Multiset ℂ) :
    α = Multiset.replicate (α.count 0) 0 + α.filter (· ≠ 0) := by
  conv_lhs => rw [← Multiset.filter_add_not (fun a => a = 0) α]
  rw [Multiset.filter_eq' α 0]

noncomputable abbrev P : ℂ[X] := 1 - 9 * X + 71 * X ^ 2 - 9 * 41 * X ^ 3 + 41 ^ 2 * X ^ 4

lemma natDeg_P : P.natDegree = 4 := by
  unfold P; compute_degree!

lemma deg1 (a : ℂ) (ha : a ≠ 0) : (1 - C a * X : ℂ[X]).natDegree = 1 := by
  rw [sub_eq_add_neg, ← neg_mul, ← C_neg, add_comm, show (1 : ℂ[X]) = C 1 from C_1.symm,
    natDegree_add_C, natDegree_C_mul_X _ (neg_ne_zero.mpr ha)]

lemma card_of_prod (β : Multiset ℂ) (hβ : ∀ a ∈ β, a ≠ 0) :
    ((β.map fun a => 1 - C a * X).prod).natDegree = Multiset.card β := by
  rw [Polynomial.natDegree_multiset_prod]
  · rw [Multiset.map_map]
    have : ∀ a ∈ β, (natDegree ∘ fun a : ℂ => 1 - C a * X) a = 1 := fun a ha => deg1 a (hβ a ha)
    rw [Multiset.map_congr rfl this, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]
  · intro h
    simp only [Multiset.mem_map] at h
    obtain ⟨a, ha, h0⟩ := h
    have := deg1 a (hβ a ha)
    rw [h0, natDegree_zero] at this
    exact zero_ne_one this

lemma setup (α : Multiset ℂ) (hα : P = (α.map fun a => 1 - C a * X).prod) :
    ∃ a b c d : ℂ, (∀ i, Wf α i = Wf {a, b, c, d} i) ∧
      a + b + c + d = 9 ∧ a * b + a * c + a * d + b * c + b * d + c * d = 71 ∧
      a * b * c + a * b * d + a * c * d + b * c * d = 9 * 41 ∧ a * b * c * d = 41 ^ 2 := by
  set β := α.filter (· ≠ 0) with hβdef
  have hsplit := split α
  have hW : ∀ i, Wf α i = Wf β i := by
    intro i; conv_lhs => rw [hsplit]
    exact Wf_replicate_zero _ _ _
  have hβprod : P = (β.map fun a => 1 - C a * X).prod := by
    rw [hα]; conv_lhs => rw [hsplit]
    exact prod_cons_zero _ _
  have hβ0 : ∀ a ∈ β, a ≠ 0 := fun a ha => (Multiset.mem_filter.mp ha).2
  have hcard : Multiset.card β = 4 := by rw [← card_of_prod β hβ0, ← hβprod, natDeg_P]
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card β)
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem ha
  have ht3 : Multiset.card t = 3 := by rw [ht, Multiset.card_cons] at hcard; omega
  obtain ⟨b, c, d, rfl⟩ := Multiset.card_eq_three.mp ht3
  have hβeq : β = {a, b, c, d} := by rw [ht]; rfl
  have key : P = 1 - C (a + b + c + d) * X + C (a * b + a * c + a * d + b * c + b * d + c * d) * X ^ 2
      - C (a * b * c + a * b * d + a * c * d + b * c * d) * X ^ 3 + C (a * b * c * d) * X ^ 4 := by
    rw [hβprod, hβeq]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton, map_add, map_mul]
    ring
  have key' : C (a + b + c + d - 9) * X ^ 1 + C (71 - (a * b + a * c + a * d + b * c + b * d + c * d)) * X ^ 2
      + C (a * b * c + a * b * d + a * c * d + b * c * d - 9 * 41) * X ^ 3
      + C (41 ^ 2 - a * b * c * d) * X ^ 4 = 0 := by
    have hP : P = 1 - C 9 * X + C 71 * X ^ 2 - C (9 * 41) * X ^ 3 + C (41 ^ 2) * X ^ 4 := by
      simp only [P, map_mul, map_pow, map_ofNat]
    rw [hP] at key
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at key ⊢
    linear_combination key
  have cf : ∀ k, coeff (C (a + b + c + d - 9) * X ^ 1 + C (71 - (a * b + a * c + a * d + b * c + b * d + c * d)) * X ^ 2
      + C (a * b * c + a * b * d + a * c * d + b * c * d - 9 * 41) * X ^ 3
      + C (41 ^ 2 - a * b * c * d) * X ^ 4) k = 0 := fun k => by rw [key', coeff_zero]
  have c1 := cf 1
  have c2 := cf 2
  have c3 := cf 3
  have c4 := cf 4
  simp only [coeff_add, coeff_C_mul_X_pow] at c1 c2 c3 c4
  norm_num at c1 c2 c3 c4
  refine ⟨a, b, c, d, fun i => by rw [hW, hβeq], ?_, ?_, ?_, ?_⟩
  · linear_combination c1
  · linear_combination -c2
  · linear_combination c3
  · linear_combination -c4

lemma pc1 (x : ℂ) : Multiset.powersetCard 1 ({x} : Multiset ℂ) = {{x}} := by
  simp [Multiset.powersetCard_one]

lemma pc2 (x : ℂ) : Multiset.powersetCard 2 ({x} : Multiset ℂ) = 0 :=
  Multiset.powersetCard_eq_empty _ (by simp)

lemma pc3 (x : ℂ) : Multiset.powersetCard 3 ({x} : Multiset ℂ) = 0 :=
  Multiset.powersetCard_eq_empty _ (by simp)

lemma pc4 (x : ℂ) : Multiset.powersetCard 4 ({x} : Multiset ℂ) = 0 :=
  Multiset.powersetCard_eq_empty _ (by simp)

theorem main (α : Multiset ℂ)
    (hα : (1 - 9 * Polynomial.X + 71 * Polynomial.X ^ 2 - 9 * 41 * Polynomial.X ^ 3 +
          41 ^ 2 * Polynomial.X ^ 4 : ℂ[X]) = (α.map fun a => 1 - C a * Polynomial.X).prod) :
    let W : ℕ → ℂ[X] := fun i => ((α.powersetCard i).map fun s => 1 - C s.prod * Polynomial.X).prod
    W 0 = 1 - Polynomial.X ∧
    W 1 = 1 - 3 ^ 2 * Polynomial.X + 71 * Polynomial.X ^ 2 - 3 ^ 2 * 41 * Polynomial.X ^ 3 +
      41 ^ 2 * Polynomial.X ^ 4 ∧
    W 2 = (1 - 41 * Polynomial.X) ^ 2 * (1 + 11 * Polynomial.X + 3 * 7 * 41 * Polynomial.X ^ 2 +
      11 * 41 ^ 2 * Polynomial.X ^ 3 + 41 ^ 4 * Polynomial.X ^ 4) ∧
    W 3 = 1 - 3 ^ 2 * 41 * Polynomial.X + 71 * 41 ^ 2 * Polynomial.X ^ 2 -
      3 ^ 2 * 41 ^ 4 * Polynomial.X ^ 3 + 41 ^ 6 * Polynomial.X ^ 4 ∧
    W 4 = 1 - 41 ^ 2 * Polynomial.X := by
  intro W
  obtain ⟨a, b, c, d, hW, h1, h2, h3, h4⟩ := setup α hα
  have H1 : C a + C b + C c + C d = (9 : ℂ[X]) := by
    have := congrArg C h1; simpa only [map_add, map_ofNat] using this
  have H2 : C a * C b + C a * C c + C a * C d + C b * C c + C b * C d + C c * C d = (71 : ℂ[X]) := by
    have := congrArg C h2; simpa only [map_add, map_mul, map_ofNat] using this
  have H3 : C a * C b * C c + C a * C b * C d + C a * C c * C d + C b * C c * C d = (9 * 41 : ℂ[X]) := by
    have := congrArg C h3; simpa only [map_add, map_mul, map_ofNat] using this
  have H4 : C a * C b * C c * C d = (41 ^ 2 : ℂ[X]) := by
    have := congrArg C h4; simpa only [map_mul, map_pow, map_ofNat] using this
  have hWi : ∀ i, W i = Wf {a, b, c, d} i := fun i => hW i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show Wf α 0 = _
    simp [Wf, Multiset.powersetCard_zero_left]
  · show Wf α 1 = _
    simp only [Wf, Multiset.powersetCard_one, Multiset.map_map, Function.comp_def,
      Multiset.prod_singleton]
    rw [← hα]; norm_num
  · rw [hWi]
    simp only [Wf, Multiset.insert_eq_cons, Multiset.powersetCard_cons,
      Multiset.powersetCard_zero_left, Multiset.map_add, Multiset.prod_add,
      Multiset.map_cons, Multiset.map_singleton, Multiset.map_zero, Multiset.prod_cons,
      Multiset.prod_singleton, Multiset.prod_zero, Function.comp_apply, Multiset.powersetCard_zero_right,
      Multiset.cons_zero, Nat.reduceAdd, mul_one, one_mul, pc1, pc2, map_mul]
    set A := C a; set B := C b; set Cc := C c; set D := C d
    linear_combination (-X) * H2
      + X ^ 2 * ((A * B * Cc + A * B * D + A * Cc * D + B * Cc * D) * H1 + 9 * H3 - H4)
      - X ^ 3 * ((A * B * Cc * D) * ((A + B + Cc + D) + 9) * H1 + 81 * H4
          + ((A * B * Cc + A * B * D + A * Cc * D + B * Cc * D) + 369) * H3
          - 2 * (A * B * Cc * D) * H2 - 142 * H4)
      + X ^ 4 * ((A * B * Cc * D) * ((A * B * Cc + A * B * D + A * Cc * D + B * Cc * D) * H1
          + 9 * H3 - H4) + 1640 * H4)
      - X ^ 5 * ((A * B * Cc * D) ^ 2 * H2 + 71 * ((A * B * Cc * D) + 1681) * H4)
      + X ^ 6 * (((A * B * Cc * D) ^ 2 + 1681 * (A * B * Cc * D) + 1681 ^ 2) * H4)
  · rw [hWi]
    simp only [Wf, Multiset.insert_eq_cons, Multiset.powersetCard_cons,
      Multiset.powersetCard_zero_left, Multiset.map_add, Multiset.prod_add,
      Multiset.map_cons, Multiset.map_singleton, Multiset.map_zero, Multiset.prod_cons,
      Multiset.prod_singleton, Multiset.prod_zero, Function.comp_apply, Multiset.powersetCard_zero_right,
      Multiset.cons_zero, Nat.reduceAdd, mul_one, one_mul, pc1, pc2, pc3, map_mul]
    set A := C a; set B := C b; set Cc := C c; set D := C d
    linear_combination (-X) * H3 + X ^ 2 * ((A * B * Cc * D) * H2 + 71 * H4)
      - X ^ 3 * ((A * B * Cc * D) ^ 2 * H1 + 9 * ((A * B * Cc * D) + 1681) * H4)
      + X ^ 4 * (((A * B * Cc * D) ^ 2 + 1681 * (A * B * Cc * D) + 1681 ^ 2) * H4)
  · rw [hWi]
    simp only [Wf, Multiset.insert_eq_cons, Multiset.powersetCard_cons,
      Multiset.powersetCard_zero_left, Multiset.map_add, Multiset.prod_add,
      Multiset.map_cons, Multiset.map_singleton, Multiset.map_zero, Multiset.prod_cons,
      Multiset.prod_singleton, Multiset.prod_zero, Function.comp_apply, Multiset.powersetCard_zero_right,
      Multiset.cons_zero, Nat.reduceAdd, mul_one, one_mul, pc1, pc2, pc3, pc4, map_mul]
    linear_combination (-X) * H4

end WEJ

open Polynomial in
theorem solution (α : Multiset ℂ)
    (hα : (1 - 9 * Polynomial.X + 71 * Polynomial.X ^ 2 - 9 * 41 * Polynomial.X ^ 3 +
          41 ^ 2 * Polynomial.X ^ 4 : ℂ[X]) = (α.map fun a => 1 - C a * Polynomial.X).prod) :
    let W : ℕ → ℂ[X] := fun i => ((α.powersetCard i).map fun s => 1 - C s.prod * Polynomial.X).prod
    W 0 = 1 - Polynomial.X ∧
    W 1 = 1 - 3 ^ 2 * Polynomial.X + 71 * Polynomial.X ^ 2 - 3 ^ 2 * 41 * Polynomial.X ^ 3 +
      41 ^ 2 * Polynomial.X ^ 4 ∧
    W 2 = (1 - 41 * Polynomial.X) ^ 2 * (1 + 11 * Polynomial.X + 3 * 7 * 41 * Polynomial.X ^ 2 +
      11 * 41 ^ 2 * Polynomial.X ^ 3 + 41 ^ 4 * Polynomial.X ^ 4) ∧
    W 3 = 1 - 3 ^ 2 * 41 * Polynomial.X + 71 * 41 ^ 2 * Polynomial.X ^ 2 -
      3 ^ 2 * 41 ^ 4 * Polynomial.X ^ 3 + 41 ^ 6 * Polynomial.X ^ 4 ∧
    W 4 = 1 - 41 ^ 2 * Polynomial.X :=
  WEJ.main α hα

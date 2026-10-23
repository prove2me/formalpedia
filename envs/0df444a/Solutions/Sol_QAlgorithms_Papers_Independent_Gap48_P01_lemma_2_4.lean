-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P01.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:29:19.289416+00:00
-- url     : https://prove2.me/submissions/d8c45b28-e9fd-4196-9542-98b0bca0e717

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01

namespace X8B24

open Finset

lemma icc_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (p : ℕ) :
    ∑ s ∈ Icc 1 p, f s = ∑ t ∈ range p, f (t+1) := by
  induction p with
  | zero => simp
  | succ p ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

lemma icc0_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (p : ℕ) :
    ∑ s ∈ Icc 0 p, f s = ∑ t ∈ range (p+1), f t := by
  induction p with
  | zero => simp
  | succ p ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ _ (p+1)]

set_option linter.unusedSectionVars false

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  (δ : R) (x xi u ui v vi e : A)
  (hx1 : x * xi = 1) (hx2 : xi * x = 1) (hu1 : u * ui = 1) (hu2 : ui * u = 1)
  (hsk : x - xi = δ • (1 - e)) (hxe : x * e = e * x)
  (hv : v = x * u * x) (hvi : vi = xi * ui * xi)

include hsk in
lemma xi_eq : xi = x - δ • (1 - e) := by rw [← hsk]; abel

include hsk in
lemma x_eq : x = xi + δ • (1 - e) := by rw [← hsk]; abel

include hx1 hsk hv in
lemma b1 : x * u = v * x - δ • v + δ • (v * e) := by
  have : v * xi = x * u := by rw [hv, mul_assoc, hx1, mul_one]
  rw [← this, xi_eq δ x xi e hsk]
  simp only [mul_sub, smul_sub, mul_smul_comm, mul_one]; abel

include hx2 hsk hvi in
lemma b2 : x * ui = vi * x + δ • ui - δ • (e * ui) := by
  have h1 : vi * x = xi * ui := by rw [hvi, mul_assoc, hx2, mul_one]
  rw [h1]
  conv_lhs => rw [x_eq δ x xi e hsk]
  simp only [add_mul, smul_mul_assoc, sub_mul, one_mul, smul_sub]; abel

include hx1 hsk hxe hv in
lemma b5 : x * x = 1 + δ • x - δ • (e * x) := by
  conv_lhs => rw [show x * x = x * (xi + δ • (1 - e)) by rw [← x_eq δ x xi e hsk]]
  rw [mul_add, hx1, mul_smul_comm, mul_sub, mul_one, hxe, smul_sub]; abel

include hx1 hsk hxe hv in
lemma b3 : x * v = u * x + δ • v - δ • (e * v) := by
  have h2 : x * v = x * x * (u * x) := by rw [hv]; simp only [mul_assoc]
  rw [h2, b5 δ x xi u v e hx1 hsk hxe hv, hv]
  simp only [add_mul, smul_mul_assoc, sub_mul, one_mul, mul_assoc]

include hx1 hsk hvi in
lemma b4 : x * vi = ui * x - δ • ui + δ • (ui * e) := by
  have h1 : x * vi = ui * xi := by rw [hvi, ← mul_assoc, ← mul_assoc, hx1, one_mul]
  rw [h1, xi_eq δ x xi e hsk]
  simp only [mul_sub, smul_sub, mul_smul_comm, mul_one]; abel

section ind
include hx1 hx2 hsk hxe hv hvi

lemma g25 (p : ℕ) : x * u^p = v^p * x - δ • ∑ t ∈ range p, v^(t+1) * u^(p-(t+1)) +
    δ • ∑ t ∈ range p, v^(t+1) * e * u^(p-(t+1)) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hS1 : ∑ t ∈ range (p+1), v^(t+1) * u^(p+1-(t+1)) =
        (∑ t ∈ range p, v^(t+1) * u^(p-(t+1))) * u + v^(p+1) := by
      rw [sum_range_succ, sum_mul]; congr 1
      · apply sum_congr rfl; intro t ht; rw [mem_range] at ht
        rw [show p+1-(t+1) = p-(t+1)+1 by omega, pow_succ _ (p-(t+1))]; simp only [mul_assoc]
      · simp
    have hS2 : ∑ t ∈ range (p+1), v^(t+1) * e * u^(p+1-(t+1)) =
        (∑ t ∈ range p, v^(t+1) * e * u^(p-(t+1))) * u + v^(p+1) * e := by
      rw [sum_range_succ, sum_mul]; congr 1
      · apply sum_congr rfl; intro t ht; rw [mem_range] at ht
        rw [show p+1-(t+1) = p-(t+1)+1 by omega, pow_succ _ (p-(t+1))]; simp only [mul_assoc]
      · simp
    rw [hS1, hS2, pow_succ u, ← mul_assoc, ih]
    have h := b1 δ x xi u v e hx1 hsk hv
    simp only [sub_mul, add_mul, smul_mul_assoc, mul_assoc, h, smul_add, mul_add, mul_sub,
      mul_smul_comm, pow_succ]
    abel

lemma g26 (p : ℕ) : x * ui^p = vi^p * x + δ • ∑ t ∈ range p, vi^(p-(t+1)) * ui^(t+1) -
    δ • ∑ t ∈ range p, vi^(p-(t+1)) * e * ui^(t+1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hS1 : ∑ t ∈ range (p+1), vi^(p+1-(t+1)) * ui^(t+1) =
        vi * (∑ t ∈ range p, vi^(p-(t+1)) * ui^(t+1)) + ui^(p+1) := by
      rw [sum_range_succ, mul_sum]; congr 1
      · apply sum_congr rfl; intro t ht; rw [mem_range] at ht
        rw [show p+1-(t+1) = p-(t+1)+1 by omega, pow_succ' _ (p-(t+1))]; simp only [mul_assoc]
      · simp
    have hS2 : ∑ t ∈ range (p+1), vi^(p+1-(t+1)) * e * ui^(t+1) =
        vi * (∑ t ∈ range p, vi^(p-(t+1)) * e * ui^(t+1)) + e * ui^(p+1) := by
      rw [sum_range_succ, mul_sum]; congr 1
      · apply sum_congr rfl; intro t ht; rw [mem_range] at ht
        rw [show p+1-(t+1) = p-(t+1)+1 by omega, pow_succ' _ (p-(t+1))]; simp only [mul_assoc]
      · simp
    rw [hS1, hS2, pow_succ' ui, ← mul_assoc, b2 δ x xi ui vi e hx2 hsk hvi]
    simp only [sub_mul, add_mul, smul_mul_assoc, mul_assoc, ih, smul_add, mul_add, mul_sub,
      mul_smul_comm, pow_succ']
    abel

lemma g27 (p : ℕ) : x * v^p = u^p * x + δ • ∑ t ∈ range p, u^(p-(t+1)) * v^(t+1) -
    δ • ∑ t ∈ range p, u^(p-(t+1)) * e * v^(t+1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hS1 : ∑ t ∈ range (p+1), u^(p+1-(t+1)) * v^(t+1) =
        u * (∑ t ∈ range p, u^(p-(t+1)) * v^(t+1)) + v^(p+1) := by
      rw [sum_range_succ, mul_sum]; congr 1
      · apply sum_congr rfl; intro t ht; rw [mem_range] at ht
        rw [show p+1-(t+1) = p-(t+1)+1 by omega, pow_succ' _ (p-(t+1))]; simp only [mul_assoc]
      · simp
    have hS2 : ∑ t ∈ range (p+1), u^(p+1-(t+1)) * e * v^(t+1) =
        u * (∑ t ∈ range p, u^(p-(t+1)) * e * v^(t+1)) + e * v^(p+1) := by
      rw [sum_range_succ, mul_sum]; congr 1
      · apply sum_congr rfl; intro t ht; rw [mem_range] at ht
        rw [show p+1-(t+1) = p-(t+1)+1 by omega, pow_succ' _ (p-(t+1))]; simp only [mul_assoc]
      · simp
    rw [hS1, hS2, pow_succ' v, ← mul_assoc, b3 δ x xi u v e hx1 hsk hxe hv]
    simp only [sub_mul, add_mul, smul_mul_assoc, mul_assoc, ih, smul_add, mul_add, mul_sub,
      mul_smul_comm, pow_succ']
    abel

lemma g27' (p : ℕ) : x * v^p = u^p * x + δ • ∑ t ∈ range p, u^t * v^(p-t) -
    δ • ∑ t ∈ range p, u^t * e * v^(p-t) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hS1 : ∑ t ∈ range (p+1), u^t * v^(p+1-t) =
        (∑ t ∈ range p, u^t * v^(p-t)) * v + u^p * v := by
      rw [sum_range_succ, sum_mul]; congr 1
      · apply sum_congr rfl; intro t ht; rw [mem_range] at ht
        rw [show p+1-t = p-t+1 by omega, pow_succ _ (p-t)]; simp only [mul_assoc]
      · simp
    have hS2 : ∑ t ∈ range (p+1), u^t * e * v^(p+1-t) =
        (∑ t ∈ range p, u^t * e * v^(p-t)) * v + u^p * e * v := by
      rw [sum_range_succ, sum_mul]; congr 1
      · apply sum_congr rfl; intro t ht; rw [mem_range] at ht
        rw [show p+1-t = p-t+1 by omega, pow_succ _ (p-t)]; simp only [mul_assoc]
      · simp
    rw [hS1, hS2, pow_succ v, ← mul_assoc, ih]
    have h := b3 δ x xi u v e hx1 hsk hxe hv
    simp only [sub_mul, add_mul, smul_mul_assoc, mul_assoc, h, smul_add, mul_add, mul_sub,
      mul_smul_comm, pow_succ]
    abel

lemma g28 (p : ℕ) : x * vi^p = ui^p * x - δ • ∑ t ∈ range p, ui^(t+1) * vi^(p-(t+1)) +
    δ • ∑ t ∈ range p, ui^(t+1) * e * vi^(p-(t+1)) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hS1 : ∑ t ∈ range (p+1), ui^(t+1) * vi^(p+1-(t+1)) =
        ui * (∑ t ∈ range p, ui^(t+1) * vi^(p-(t+1))) + ui * vi^p := by
      rw [sum_range_succ', mul_sum]; congr 1
      · apply sum_congr rfl; intro t ht; rw [mem_range] at ht
        rw [show p+1-(t+1+1) = p-(t+1) by omega, pow_succ' ui (t+1), mul_assoc]
      · simp
    have hS2 : ∑ t ∈ range (p+1), ui^(t+1) * e * vi^(p+1-(t+1)) =
        ui * (∑ t ∈ range p, ui^(t+1) * e * vi^(p-(t+1))) + ui * e * vi^p := by
      rw [sum_range_succ', mul_sum]; congr 1
      · apply sum_congr rfl; intro t ht; rw [mem_range] at ht
        rw [show p+1-(t+1+1) = p-(t+1) by omega, pow_succ' ui (t+1)]; simp only [mul_assoc]
      · simp
    rw [hS1, hS2, pow_succ' vi, pow_succ' ui p, ← mul_assoc, b4 δ x xi ui vi e hx1 hsk hvi]
    simp only [sub_mul, add_mul, smul_mul_assoc, mul_assoc, ih, smul_add, mul_add, mul_sub,
      mul_smul_comm]
    abel

lemma g29 (q : ℕ) : x * u^(q+1) * x = v^(q+1) - δ • ∑ t ∈ range q, v^(t+1) * u^(q+1-(t+1)) * x +
    δ • ∑ t ∈ range q, v^(t+1) * e * u^(q+1-(t+1)) * x := by
  have h := g25 δ x xi u ui v vi e hx1 hx2 hsk hxe hv hvi (q+1)
  rw [sum_range_succ, sum_range_succ (fun t => v^(t+1) * e * u^(q+1-(t+1)))] at h
  simp only [Nat.sub_self, pow_zero, mul_one] at h
  rw [h]
  have h5 := b5 δ x xi u v e hx1 hsk hxe hv
  simp only [sub_mul, add_mul, smul_mul_assoc, sum_mul, mul_assoc, h5, smul_add, mul_add, mul_sub,
    mul_smul_comm, smul_sub, mul_one]
  abel

lemma g30 (q : ℕ) : x * u^(q+1) * x = v^(q+1) - δ • ∑ t ∈ range q, x * u^(t+1) * v^(q+1-(t+1)) +
    δ • ∑ t ∈ range q, x * u^(t+1) * e * v^(q+1-(t+1)) := by
  have h := g27' δ x xi u ui v vi e hx1 hx2 hsk hxe hv hvi (q+1)
  rw [sum_range_succ', sum_range_succ' (fun t => u^t * e * v^(q+1-t))] at h
  simp only [Nat.sub_zero, pow_zero, one_mul] at h
  have key : x * u^(q+1) * x = x * (x * v^(q+1)) -
      δ • (x * ((∑ t ∈ range q, u^(t+1) * v^(q+1-(t+1))) + v^(q+1))) +
      δ • (x * ((∑ t ∈ range q, u^(t+1) * e * v^(q+1-(t+1))) + e * v^(q+1))) := by
    rw [h]; simp only [mul_add, mul_sub, mul_smul_comm, mul_assoc]; abel
  rw [key, ← mul_assoc x x, b5 δ x xi u v e hx1 hsk hxe hv]
  simp only [sub_mul, add_mul, smul_mul_assoc, mul_sum, mul_assoc, smul_add, mul_add, mul_sub,
    mul_smul_comm, smul_sub, one_mul, ← hxe]
  abel

lemma g31 (p : ℕ) : x * ui^p * x = vi^p + δ • ∑ t ∈ range (p+1), vi^(p-t) * ui^t * x -
    δ • ∑ t ∈ range (p+1), vi^(p-t) * e * ui^t * x := by
  have h := g26 δ x xi u ui v vi e hx1 hx2 hsk hxe hv hvi p
  rw [sum_range_succ', sum_range_succ' (fun t => vi^(p-t) * e * ui^t * x)]
  simp only [Nat.sub_zero, pow_zero, mul_one]
  rw [h]
  have h5 := b5 δ x xi u v e hx1 hsk hxe hv
  simp only [sub_mul, add_mul, smul_mul_assoc, sum_mul, mul_assoc, h5, smul_add, mul_add, mul_sub,
    mul_smul_comm, smul_sub, mul_one]
  abel

lemma g32 (p : ℕ) : x * ui^p * x = vi^p + δ • ∑ t ∈ range (p+1), x * ui^t * vi^(p-t) -
    δ • ∑ t ∈ range (p+1), x * ui^t * e * vi^(p-t) := by
  have h := g28 δ x xi u ui v vi e hx1 hx2 hsk hxe hv hvi p
  have key : x * ui^p * x = x * (x * vi^p) +
      δ • (x * (∑ t ∈ range p, ui^(t+1) * vi^(p-(t+1)))) -
      δ • (x * (∑ t ∈ range p, ui^(t+1) * e * vi^(p-(t+1)))) := by
    rw [h]; simp only [mul_add, mul_sub, mul_smul_comm, mul_assoc]; abel
  rw [key, ← mul_assoc x x, b5 δ x xi u v e hx1 hsk hxe hv,
    sum_range_succ', sum_range_succ' (fun t => x * ui^t * e * vi^(p-t))]
  simp only [sub_mul, add_mul, smul_mul_assoc, mul_sum, mul_assoc, smul_add, mul_add, mul_sub,
    mul_smul_comm, smul_sub, one_mul, ← hxe, Nat.sub_zero, pow_zero]
  abel

end ind

end X8B24

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8B4

open Finset X8B24

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

lemma rel {a b : FreeAlgebra R (CyclotomicLetter n)} (h : NonsplitBMWRel P n a b) :
    presentationMap P n a = presentationMap P n b :=
  RingQuot.mkAlgHom_rel R h

lemma jpN (j q : ℕ) (a : ℤ) (h : a = q) : JPower P n j a = JM P n false j ^ q := by
  subst h; simp [JPower]

lemma jpI (j q : ℕ) (a : ℤ) (h : a = -(q:ℤ)) : JPower P n j a = JM P n true j ^ q := by
  subst h; unfold JPower
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · rw [if_neg (by omega)]; simp

lemma jpN' (j : ℕ) (a : ℤ) (h : 0 ≤ a) : JPower P n j a = JM P n false j ^ a.toNat := by
  simp [JPower, h]

lemma jpI' (j : ℕ) (a : ℤ) (h : a ≤ 0) : JPower P n j a = JM P n true j ^ (-a).toNat := by
  unfold JPower
  rcases eq_or_lt_of_le h with rfl | h'
  · simp
  · rw [if_neg (by omega)]

theorem x8_main (i p : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    (X P n i false * JPower P n i p = JPower P n (i+1) p * X P n i false -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n (i+1) s * JPower P n i ((p:ℤ)-s)) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n (i+1) s * E P n i * JPower P n i ((p:ℤ)-s))) ∧
    (X P n i false * JPower P n i (-(p:ℤ)) = JPower P n (i+1) (-(p:ℤ)) * X P n i false +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n (i+1) ((s:ℤ)-p) * JPower P n i (-(s:ℤ))) -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n (i+1) ((s:ℤ)-p) * E P n i * JPower P n i (-(s:ℤ)))) ∧
    (X P n i false * JPower P n (i+1) p = JPower P n i p * X P n i false +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n i ((p:ℤ)-s) * JPower P n (i+1) s) -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n i ((p:ℤ)-s) * E P n i * JPower P n (i+1) s)) ∧
    (X P n i false * JPower P n (i+1) (-(p:ℤ)) = JPower P n i (-(p:ℤ)) * X P n i false -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n i (-(s:ℤ)) * JPower P n (i+1) ((s:ℤ)-p)) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n i (-(s:ℤ)) * E P n i * JPower P n (i+1) ((s:ℤ)-p))) ∧
    (1 ≤ p → X P n i false * JPower P n i p * X P n i false = JPower P n (i+1) p -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 (p-1), JPower P n (i+1) s * JPower P n i ((p:ℤ)-s) * X P n i false) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 (p-1), JPower P n (i+1) s * E P n i * JPower P n i ((p:ℤ)-s) * X P n i false)) ∧
    (1 ≤ p → X P n i false * JPower P n i p * X P n i false = JPower P n (i+1) p -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 (p-1), X P n i false * JPower P n i s * JPower P n (i+1) ((p:ℤ)-s)) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 (p-1), X P n i false * JPower P n i s * E P n i * JPower P n (i+1) ((p:ℤ)-s))) ∧
    (X P n i false * JPower P n i (-(p:ℤ)) * X P n i false = JPower P n (i+1) (-(p:ℤ)) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 0 p, JPower P n (i+1) ((s:ℤ)-p) * JPower P n i (-(s:ℤ)) * X P n i false) -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 0 p, JPower P n (i+1) ((s:ℤ)-p) * E P n i * JPower P n i (-(s:ℤ)) * X P n i false)) ∧
    (X P n i false * JPower P n i (-(p:ℤ)) * X P n i false = JPower P n (i+1) (-(p:ℤ)) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 0 p, X P n i false * JPower P n i (-(s:ℤ)) * JPower P n (i+1) ((s:ℤ)-p)) -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 0 p, X P n i false * JPower P n i (-(s:ℤ)) * E P n i * JPower P n (i+1) ((s:ℤ)-p))) := by
  have r0 : 1 ≤ i ∧ i < n := ⟨hi, hin⟩
  have hx1 : X P n i false * X P n i true = 1 := by
    have := rel P n (NonsplitBMWRel.invL i r0); simpa [X, map_mul] using this
  have hx2 : X P n i true * X P n i false = 1 := by
    have := rel P n (NonsplitBMWRel.invR i r0); simpa [X, map_mul] using this
  have hsk : X P n i false - X P n i true = skeinDelta P • (1 - E P n i) := by
    have := rel P n (NonsplitBMWRel.skein i r0)
    rw [Algebra.smul_def]; simpa [X, E, map_mul, map_sub] using this
  have hxe : X P n i false * E P n i = E P n i * X P n i false := by
    have h1 := rel P n (NonsplitBMWRel.xe i r0)
    have h2 := rel P n (NonsplitBMWRel.ex i r0)
    simp only [map_mul, AlgHom.commutes] at h1 h2
    exact (h1.trans h2.symm)
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hv : JM P n false (m+1+1) = X P n (m+1) false * JM P n false (m+1) * X P n (m+1) false := rfl
  have hvi : JM P n true (m+1+1) = X P n (m+1) true * JM P n true (m+1) * X P n (m+1) true := rfl
  simp only [← Algebra.smul_def]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [icc_range, icc_range, jpN P n (m+1) p p rfl, jpN P n (m+1+1) p p rfl]
    convert g25 (skeinDelta P) _ _ _ (JM P n true (m+1)) _ _ _ hx1 hx2 hsk hxe hv hvi p using 3
    all_goals first
      | (refine sum_congr rfl fun t ht => ?_; rw [mem_range] at ht)
      | (refine congrArg (skeinDelta P • ·) (sum_congr rfl fun t ht => ?_); rw [mem_range] at ht)
    all_goals (rw [jpN' P n (m+1+1), jpN' P n (m+1)])
    all_goals first | omega | (congr <;> omega)
  · rw [icc_range, icc_range, jpI P n (m+1) p _ rfl, jpI P n (m+1+1) p _ rfl]
    convert g26 (skeinDelta P) _ _ (JM P n false (m+1)) _ _ _ _ hx1 hx2 hsk hxe hv hvi p using 3
    all_goals first
      | (refine sum_congr rfl fun t ht => ?_; rw [mem_range] at ht)
      | (refine congrArg (skeinDelta P • ·) (sum_congr rfl fun t ht => ?_); rw [mem_range] at ht)
    all_goals (rw [jpI' P n (m+1+1), jpI' P n (m+1)])
    all_goals first | omega | (congr <;> omega)
  · rw [icc_range, icc_range, jpN P n (m+1) p p rfl, jpN P n (m+1+1) p p rfl]
    convert g27 (skeinDelta P) _ _ _ (JM P n true (m+1)) _ _ _ hx1 hx2 hsk hxe hv hvi p using 3
    all_goals first
      | (refine sum_congr rfl fun t ht => ?_; rw [mem_range] at ht)
      | (refine congrArg (skeinDelta P • ·) (sum_congr rfl fun t ht => ?_); rw [mem_range] at ht)
    all_goals (rw [jpN' P n (m+1+1), jpN' P n (m+1)])
    all_goals first | omega | (congr <;> omega)
  · rw [icc_range, icc_range, jpI P n (m+1) p _ rfl, jpI P n (m+1+1) p _ rfl]
    convert g28 (skeinDelta P) _ _ (JM P n false (m+1)) _ _ _ _ hx1 hx2 hsk hxe hv hvi p using 3
    all_goals first
      | (refine sum_congr rfl fun t ht => ?_; rw [mem_range] at ht)
      | (refine congrArg (skeinDelta P • ·) (sum_congr rfl fun t ht => ?_); rw [mem_range] at ht)
    all_goals (rw [jpI' P n (m+1+1), jpI' P n (m+1)])
    all_goals first | omega | (congr <;> omega)
  · intro hp
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [icc_range, icc_range, jpN P n (m+1) (q+1) _ rfl, jpN P n (m+1+1) (q+1) _ rfl]
    convert g29 (skeinDelta P) _ _ _ (JM P n true (m+1)) _ _ _ hx1 hx2 hsk hxe hv hvi q using 3
    all_goals first
      | (refine sum_congr rfl fun t ht => ?_; rw [mem_range] at ht)
      | (refine congrArg (skeinDelta P • ·) (sum_congr rfl fun t ht => ?_); rw [mem_range] at ht)
    all_goals (rw [jpN' P n (m+1+1), jpN' P n (m+1)])
    all_goals first | omega | (congr <;> omega)
  · intro hp
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [icc_range, icc_range, jpN P n (m+1) (q+1) _ rfl, jpN P n (m+1+1) (q+1) _ rfl]
    convert g30 (skeinDelta P) _ _ _ (JM P n true (m+1)) _ _ _ hx1 hx2 hsk hxe hv hvi q using 3
    all_goals first
      | (refine sum_congr rfl fun t ht => ?_; rw [mem_range] at ht)
      | (refine congrArg (skeinDelta P • ·) (sum_congr rfl fun t ht => ?_); rw [mem_range] at ht)
    all_goals (rw [jpN' P n (m+1+1), jpN' P n (m+1)])
    all_goals first | omega | (congr <;> omega)
  · rw [icc0_range, icc0_range, jpI P n (m+1) p _ rfl, jpI P n (m+1+1) p _ rfl]
    convert g31 (skeinDelta P) _ _ (JM P n false (m+1)) _ _ _ _ hx1 hx2 hsk hxe hv hvi p using 3
    all_goals first
      | (refine sum_congr rfl fun t ht => ?_; rw [mem_range] at ht)
      | (refine congrArg (skeinDelta P • ·) (sum_congr rfl fun t ht => ?_); rw [mem_range] at ht)
    all_goals (rw [jpI' P n (m+1+1), jpI' P n (m+1)])
    all_goals first | omega | (congr <;> omega)
  · rw [icc0_range, icc0_range, jpI P n (m+1) p _ rfl, jpI P n (m+1+1) p _ rfl]
    convert g32 (skeinDelta P) _ _ (JM P n false (m+1)) _ _ _ _ hx1 hx2 hsk hxe hv hvi p using 3
    all_goals first
      | (refine sum_congr rfl fun t ht => ?_; rw [mem_range] at ht)
      | (refine congrArg (skeinDelta P • ·) (sum_congr rfl fun t ht => ?_); rw [mem_range] at ht)
    all_goals (rw [jpI' P n (m+1), jpI' P n (m+1+1)])
    all_goals first | omega | (congr <;> omega)

end X8B4

end QAlgorithms.Papers.Independent.Gap48.P01

open scoped BigOperators Classical in
open QAlgorithms.Papers.Independent.Gap48.P01 in
theorem solution {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ) (i p : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    (X P n i false * JPower P n i p = JPower P n (i+1) p * X P n i false -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n (i+1) s * JPower P n i ((p:ℤ)-s)) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n (i+1) s * E P n i * JPower P n i ((p:ℤ)-s))) ∧
    (X P n i false * JPower P n i (-(p:ℤ)) = JPower P n (i+1) (-(p:ℤ)) * X P n i false +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n (i+1) ((s:ℤ)-p) * JPower P n i (-(s:ℤ))) -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n (i+1) ((s:ℤ)-p) * E P n i * JPower P n i (-(s:ℤ)))) ∧
    (X P n i false * JPower P n (i+1) p = JPower P n i p * X P n i false +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n i ((p:ℤ)-s) * JPower P n (i+1) s) -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n i ((p:ℤ)-s) * E P n i * JPower P n (i+1) s)) ∧
    (X P n i false * JPower P n (i+1) (-(p:ℤ)) = JPower P n i (-(p:ℤ)) * X P n i false -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n i (-(s:ℤ)) * JPower P n (i+1) ((s:ℤ)-p)) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 p, JPower P n i (-(s:ℤ)) * E P n i * JPower P n (i+1) ((s:ℤ)-p))) ∧
    (1 ≤ p → X P n i false * JPower P n i p * X P n i false = JPower P n (i+1) p -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 (p-1), JPower P n (i+1) s * JPower P n i ((p:ℤ)-s) * X P n i false) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 (p-1), JPower P n (i+1) s * E P n i * JPower P n i ((p:ℤ)-s) * X P n i false)) ∧
    (1 ≤ p → X P n i false * JPower P n i p * X P n i false = JPower P n (i+1) p -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 (p-1), X P n i false * JPower P n i s * JPower P n (i+1) ((p:ℤ)-s)) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 1 (p-1), X P n i false * JPower P n i s * E P n i * JPower P n (i+1) ((p:ℤ)-s))) ∧
    (X P n i false * JPower P n i (-(p:ℤ)) * X P n i false = JPower P n (i+1) (-(p:ℤ)) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 0 p, JPower P n (i+1) ((s:ℤ)-p) * JPower P n i (-(s:ℤ)) * X P n i false) -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 0 p, JPower P n (i+1) ((s:ℤ)-p) * E P n i * JPower P n i (-(s:ℤ)) * X P n i false)) ∧
    (X P n i false * JPower P n i (-(p:ℤ)) * X P n i false = JPower P n (i+1) (-(p:ℤ)) +
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 0 p, X P n i false * JPower P n i (-(s:ℤ)) * JPower P n (i+1) ((s:ℤ)-p)) -
      algebraMap R _ (skeinDelta P) * (∑ s ∈ Finset.Icc 0 p, X P n i false * JPower P n i (-(s:ℤ)) * E P n i * JPower P n (i+1) ((s:ℤ)-p))) :=
  X8B4.x8_main P n i p hi hin

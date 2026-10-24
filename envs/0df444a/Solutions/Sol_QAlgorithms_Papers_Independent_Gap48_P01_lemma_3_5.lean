-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P01.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T08:10:26.162019+00:00
-- url     : https://prove2.me/submissions/1212d872-0498-40db-acef-7ccc78ee4932

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P01_lemma_3_4

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


namespace X8L25

set_option linter.unusedSectionVars false

structure Sys (R A : Type*) [CommRing R] [Ring A] [Algebra R A] (n : ℕ) where
  δ : R
  lam : R
  lami : R
  hlam : lami * lam = 1
  x : ℕ → A
  xi : ℕ → A
  e : ℕ → A
  u : ℕ → Aˣ
  x_xi : ∀ i, 1 ≤ i → i < n → x i * xi i = 1
  xi_x : ∀ i, 1 ≤ i → i < n → xi i * x i = 1
  skein : ∀ i, 1 ≤ i → i < n → x i - xi i = δ • (1 - e i)
  xe : ∀ i, 1 ≤ i → i < n → x i * e i = lam • e i
  ex : ∀ i, 1 ≤ i → i < n → e i * x i = lam • e i
  sq : ∀ i, 1 ≤ i → i < n → ∃ c : R, e i * e i = c • e i
  nearL : ∀ a, 1 ≤ a → a + 1 < n → x (a+1) * x a * e (a+1) = e a * e (a+1)
  nearR : ∀ a, 1 ≤ a → a + 1 < n → e (a+1) * x a * x (a+1) = e (a+1) * e a
  triple : ∀ a, 1 ≤ a → a + 1 < n → e (a+1) * e a * e (a+1) = e (a+1)
  urec : ∀ a, 1 ≤ a → a < n → (u (a+1) : A) = x a * u a * x a
  m9L : ∀ a, 1 ≤ a → a < n → (u a : A) * u (a+1) * e a = e a
  m9R : ∀ a, 1 ≤ a → a < n → e a * u a * u (a+1) = e a
  ucomm : ∀ j m, 1 ≤ j → j < m → m ≤ n → (u j : A) * u m = u m * u j
  ux : ∀ j m, 1 ≤ j → j < m → m < n → (u j : A) * x m = x m * u j
  ue : ∀ j m, 1 ≤ j → j < m → m < n → (u j : A) * e m = e m * u j
  base : 1 < n → ∀ p : ℤ, ∃ c : R, e 1 * ↑(u 1 ^ p) * e 1 = c • e 1

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {n : ℕ}

inductive IsMon (u : ℕ → Aˣ) : ℕ → A → Prop
  | base : IsMon u 1 1
  | step (i : ℕ) (m : A) (t : ℤ) : IsMon u i m → IsMon u (i+1) (m * ↑(u i ^ t))

namespace IsMon
variable {u : ℕ → Aˣ}

lemma pos {i : ℕ} {m : A} (h : IsMon u i m) : 1 ≤ i := by
  cases h <;> omega

lemma inv_step {i : ℕ} {m : A} (h : IsMon u (i+1) m) (hi : 1 ≤ i) :
    ∃ m0, ∃ t : ℤ, IsMon u i m0 ∧ m = m0 * ↑(u i ^ t) := by
  generalize hk : i + 1 = k at h
  cases h with
  | base => omega
  | step j m0 t h0 =>
    obtain rfl : j = i := by omega
    exact ⟨m0, t, h0, rfl⟩

lemma mul_pow {i : ℕ} {m : A} (h : IsMon u (i+1) m) (hi : 1 ≤ i) (w : ℤ) :
    IsMon u (i+1) (m * ↑(u i ^ w)) := by
  obtain ⟨m0, t, h0, rfl⟩ := h.inv_step hi
  have := IsMon.step i m0 (t + w) h0
  rwa [zpow_add, Units.val_mul, ← mul_assoc] at this

lemma one : ∀ i, 1 ≤ i → IsMon u i (1 : A) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => exact IsMon.base
  | succ i hi ih => simpa using IsMon.step i 1 0 ih

lemma comm {i : ℕ} {m : A} (h : IsMon u i m) (y : A)
    (hy : ∀ j, 1 ≤ j → j < i → Commute (u j : A) y) : Commute m y := by
  induction h with
  | base => exact Commute.one_left y
  | step i m t h ih =>
    exact (ih (fun j hj hji => hy j hj (by omega))).mul_left
      ((hy i h.pos (by omega)).units_zpow_left t)

lemma of_inv {i : ℕ} {m : A} (h : IsMon (fun j => (u j)⁻¹) i m) : IsMon u i m := by
  induction h with
  | base => exact IsMon.base
  | step i m t h ih =>
    have := IsMon.step i m (-t) ih
    simpa [inv_zpow'] using this

end IsMon

lemma span_map {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    {s : Set M} {Q : Submodule R N} (L : M →ₗ[R] N) (h : ∀ z ∈ s, L z ∈ Q) {z : M}
    (hz : z ∈ Submodule.span R s) : L z ∈ Q :=
  (Submodule.span_le.mpr (fun z hz => h z hz) : Submodule.span R s ≤ Q.comap L) hz

lemma fix_left (w : Aˣ) (e : A) (h : (w : A) * e = e) (t : ℤ) : (↑(w ^ t) : A) * e = e := by
  have h' : (↑w⁻¹ : A) * e = e := by
    calc (↑w⁻¹ : A) * e = ↑w⁻¹ * (↑w * e) := by rw [h]
    _ = e := by rw [← mul_assoc, Units.inv_mul, one_mul]
  induction t using Int.induction_on with
  | zero => simp
  | succ t ih => rw [zpow_add_one, Units.val_mul, mul_assoc, h, ih]
  | pred t ih => rw [zpow_sub_one, Units.val_mul, mul_assoc, h', ih]

lemma fix_right (w : Aˣ) (e : A) (h : e * (w : A) = e) (t : ℤ) : e * (↑(w ^ t) : A) = e := by
  have h' : e * (↑w⁻¹ : A) = e := by
    calc e * (↑w⁻¹ : A) = (e * ↑w) * ↑w⁻¹ := by rw [h]
    _ = e := by rw [mul_assoc, Units.mul_inv, mul_one]
  induction t using Int.induction_on with
  | zero => simp
  | succ t ih =>
    rw [show (t:ℤ) + 1 = 1 + t by ring, zpow_add, zpow_one, Units.val_mul, ← mul_assoc, h, ih]
  | pred t ih =>
    rw [show (-(t:ℤ) - 1) = -1 + -(t:ℤ) by ring, zpow_add, zpow_neg_one, Units.val_mul,
      ← mul_assoc, h', ih]

namespace Sys
variable (S : Sys R A n)

def J (i : ℕ) (t : ℤ) : A := ↑(S.u i ^ t)

lemma J_add (i : ℕ) (s t : ℤ) : S.J i (s + t) = S.J i s * S.J i t := by
  simp [J, zpow_add]
lemma J_zero (i : ℕ) : S.J i 0 = 1 := by simp [J]
lemma J_one (i : ℕ) : S.J i 1 = S.u i := by simp [J]
lemma J_comm_self (i : ℕ) (s t : ℤ) : S.J i s * S.J i t = S.J i t * S.J i s := by
  rw [← S.J_add, ← S.J_add, add_comm]

lemma cx {j m : ℕ} (hj : 1 ≤ j) (hjm : j < m) (hm : m < n) (t : ℤ) :
    Commute (S.J j t) (S.x m) :=
  (show Commute (S.u j : A) (S.x m) from S.ux j m hj hjm hm).units_zpow_left t

lemma ce {j m : ℕ} (hj : 1 ≤ j) (hjm : j < m) (hm : m < n) (t : ℤ) :
    Commute (S.J j t) (S.e m) :=
  (show Commute (S.u j : A) (S.e m) from S.ue j m hj hjm hm).units_zpow_left t

lemma cxi1 {j m : ℕ} (hj : 1 ≤ j) (hjm : j < m) (hm : m < n) :
    Commute (S.u j : A) (S.xi m) := by
  have h := S.ux j m hj hjm hm
  show _ = _
  calc (S.u j : A) * S.xi m = (S.xi m * S.x m) * S.u j * S.xi m := by
        rw [S.xi_x m (by omega) hm, one_mul]
  _ = S.xi m * (S.u j * S.x m) * S.xi m := by rw [h]; simp only [mul_assoc]
  _ = S.xi m * S.u j := by rw [mul_assoc, mul_assoc, S.x_xi m (by omega) hm, mul_one]

lemma cxi {j m : ℕ} (hj : 1 ≤ j) (hjm : j < m) (hm : m < n) (t : ℤ) :
    Commute (S.J j t) (S.xi m) := (S.cxi1 hj hjm hm).units_zpow_left t

lemma uc {j m : ℕ} (hj : 1 ≤ j) (hjm : j < m) (hm : m ≤ n) :
    Commute (S.u j) (S.u m) := Units.ext (by simpa using S.ucomm j m hj hjm hm)

lemma cJJ {j m : ℕ} (hj : 1 ≤ j) (hjm : j < m) (hm : m ≤ n) (s t : ℤ) :
    Commute (S.J j s) (S.J m t) :=
  ((show Commute (S.u j : A) (S.u m) from S.ucomm j m hj hjm hm).units_zpow_left s).units_zpow_right t

lemma m9Lz {a : ℕ} (ha : 1 ≤ a) (han : a < n) (t : ℤ) :
    S.J (a+1) t * S.e a = S.J a (-t) * S.e a := by
  have h : (↑(S.u a * S.u (a+1)) : A) * S.e a = S.e a := by
    rw [Units.val_mul]; exact S.m9L a ha han
  have key : S.J a t * S.J (a+1) t * S.e a = S.e a := by
    have := fix_left _ _ h t
    rw [(S.uc ha (by omega) (by omega)).mul_zpow, Units.val_mul] at this
    exact this
  calc S.J (a+1) t * S.e a = S.J a (-t) * (S.J a t * S.J (a+1) t * S.e a) := by
        rw [← mul_assoc, ← mul_assoc, ← S.J_add, neg_add_cancel, S.J_zero, one_mul]
  _ = S.J a (-t) * S.e a := by rw [key]

lemma m9Rz {a : ℕ} (ha : 1 ≤ a) (han : a < n) (t : ℤ) :
    S.e a * S.J (a+1) t = S.e a * S.J a (-t) := by
  have h : S.e a * (↑(S.u a * S.u (a+1)) : A) = S.e a := by
    rw [Units.val_mul, ← mul_assoc]; exact S.m9R a ha han
  have key : S.e a * (S.J a t * S.J (a+1) t) = S.e a := by
    have := fix_right _ _ h t
    rw [(S.uc ha (by omega) (by omega)).mul_zpow, Units.val_mul] at this
    exact this
  calc S.e a * S.J (a+1) t = (S.e a * (S.J a t * S.J (a+1) t)) * S.J a (-t) := by
        rw [(S.cJJ ha (by omega) (by omega) t t).eq, mul_assoc, mul_assoc, ← S.J_add,
          add_neg_cancel, S.J_zero, mul_one]
  _ = S.e a * S.J a (-t) := by rw [key]

lemma xi_eq (i : ℕ) (hi : 1 ≤ i) (hin : i < n) : S.xi i = S.x i - S.δ • (1 - S.e i) := by
  rw [← S.skein i hi hin]; abel

lemma exe {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n) :
    S.e (a+1) * S.x a * S.e (a+1) = S.lami • S.e (a+1) := by
  have h1 : S.e (a+1) * S.x a * S.x (a+1) * S.e (a+1) = S.e (a+1) := by
    rw [S.nearR a ha han, S.triple a ha han]
  have h2 : S.e (a+1) * S.x a * S.x (a+1) * S.e (a+1) =
      S.lam • (S.e (a+1) * S.x a * S.e (a+1)) := by
    rw [mul_assoc _ (S.x (a+1)), S.xe (a+1) (by omega) han, mul_smul_comm]
  rw [h2] at h1
  conv_rhs => rw [← h1]
  rw [smul_smul, S.hlam, one_smul]

end Sys
end X8L25


namespace X8L25

set_option linter.unusedSectionVars false

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {n : ℕ}

namespace Sys
variable (S : Sys R A n)

def T (i : ℕ) : Submodule R A := Submodule.span R {z | ∃ m, IsMon S.u i m ∧ z = m * S.e i}
def U (i : ℕ) (r : ℤ) : Submodule R A :=
  Submodule.span R {z | ∃ m, ∃ t : ℤ, IsMon S.u i m ∧ |t| ≤ r ∧ z = m * S.J i t * S.e i}

lemma T_gen {i : ℕ} {m : A} (h : IsMon S.u i m) : m * S.e i ∈ S.T i :=
  Submodule.subset_span ⟨m, h, rfl⟩

lemma U_gen {i : ℕ} {m : A} {t r : ℤ} (h : IsMon S.u i m) (ht : |t| ≤ r) :
    m * S.J i t * S.e i ∈ S.U i r :=
  Submodule.subset_span ⟨m, t, h, ht, rfl⟩

lemma U_gen1 {i : ℕ} (hi : 1 ≤ i) {t r : ℤ} (ht : |t| ≤ r) : S.J i t * S.e i ∈ S.U i r := by
  simpa using S.U_gen (IsMon.one i hi) ht

lemma T_le_U (i : ℕ) {r : ℤ} (hr : 0 ≤ r) : S.T i ≤ S.U i r := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, hm, rfl⟩
  have := S.U_gen hm (t := 0) (r := r) (by simpa using hr)
  simpa [S.J_zero] using this

lemma U_mono (i : ℕ) {r r' : ℤ} (h : r ≤ r') : S.U i r ≤ S.U i r' := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, t, hm, ht, rfl⟩
  exact S.U_gen hm (ht.trans h)

lemma monc {i : ℕ} {m : A} (h : IsMon S.u i m) (y : A)
    (hy : ∀ j, 1 ≤ j → j < i → Commute (S.u j : A) y) : Commute m y := h.comm y hy

/-- f z f for z in U_a. -/
lemma L1 {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n) {r : ℤ} {z : A} (hz : z ∈ S.U a r) :
    S.e (a+1) * z * S.e (a+1) ∈ S.T (a+1) := by
  have := span_map (LinearMap.mulLeft R (S.e (a+1)) ∘ₗ LinearMap.mulRight R (S.e (a+1)))
    (Q := S.T (a+1)) ?_ hz
  · simpa [mul_assoc] using this
  rintro _ ⟨m, t, hm, ht, rfl⟩
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  have h1 : Commute m (S.e (a+1)) := S.monc hm _ (fun j hj hja => S.ue j (a+1) hj (by omega) han)
  have h2 : Commute (S.J a t) (S.e (a+1)) := S.ce ha (by omega) han t
  have : S.e (a+1) * (m * S.J a t * S.e a * S.e (a+1)) =
      m * S.J a t * (S.e (a+1) * S.e a * S.e (a+1)) := by
    rw [show S.e (a+1) * (m * S.J a t * S.e a * S.e (a+1)) =
      (S.e (a+1) * m) * S.J a t * S.e a * S.e (a+1) by simp only [mul_assoc], ← h1.eq,
      mul_assoc m (S.e (a+1)), ← h2.eq]
    simp only [mul_assoc]
  rw [this, S.triple a ha han]
  exact S.T_gen (IsMon.step a m t hm)

/-- right multiplication of T_(a+1) by powers of J_a. -/
lemma L2 {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n) {z : A} (hz : z ∈ S.T (a+1)) (w : ℤ) :
    z * S.J a w ∈ S.T (a+1) := by
  have := span_map (LinearMap.mulRight R (S.J a w)) (Q := S.T (a+1)) ?_ hz
  · simpa using this
  rintro _ ⟨m, hm, rfl⟩
  simp only [LinearMap.mulRight_apply]
  rw [mul_assoc, ← (S.ce ha (by omega) han w).eq, ← mul_assoc]
  exact S.T_gen (hm.mul_pow ha w)

/-- f e z for z in U_(a+1). -/
lemma L3 {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n) {r : ℤ} {z : A} (hz : z ∈ S.U (a+1) r) :
    S.e (a+1) * S.e a * z ∈ S.T (a+1) := by
  have := span_map (LinearMap.mulLeft R (S.e (a+1) * S.e a)) (Q := S.T (a+1)) ?_ hz
  · simpa [mul_assoc] using this
  rintro _ ⟨m, t, hm, ht, rfl⟩
  simp only [LinearMap.mulLeft_apply]
  obtain ⟨m0, t', hm0, rfl⟩ := hm.inv_step ha
  have h1 : Commute m0 (S.e (a+1)) :=
    S.monc hm0 _ (fun j hj hja => S.ue j (a+1) hj (by omega) han)
  have h1' : Commute m0 (S.e a) :=
    S.monc hm0 _ (fun j hj hja => S.ue j a hj hja (by omega))
  have hJ : (↑(S.u a ^ t') : A) = S.J a t' := rfl
  have h3 : S.e a * S.J (a+1) t = S.e a * S.J a (-t) := S.m9Rz ha (by omega) t
  have h4 : Commute (S.J a (-t) * S.J a t') (S.e (a+1)) :=
    (S.ce ha (by omega) han _).mul_left (S.ce ha (by omega) han _)
  have h5 : Commute (S.J a (-t + t')) (S.e (a+1)) := S.ce ha (by omega) han _
  have : S.e (a+1) * S.e a * (m0 * ↑(S.u a ^ t') * S.J (a+1) t * S.e (a+1)) =
      m0 * S.J a (-t + t') * S.e (a+1) := by
    rw [hJ, mul_assoc m0, (S.cJJ (m := a+1) ha (by omega) (by omega) t' t).eq]
    calc S.e (a+1) * S.e a * (m0 * (S.J (a+1) t * S.J a t') * S.e (a+1))
        = m0 * ((S.e (a+1) * (S.e a * S.J (a+1) t)) * S.J a t' * S.e (a+1)) := by
          simp only [mul_assoc]; rw [h1'.symm.left_comm, h1.symm.left_comm]
      _ = m0 * (S.e (a+1) * S.e a * ((S.J a (-t) * S.J a t') * S.e (a+1))) := by
          rw [h3]; simp only [mul_assoc]
      _ = m0 * ((S.e (a+1) * S.e a * S.e (a+1)) * (S.J a (-t) * S.J a t')) := by
          rw [h4.eq]; simp only [mul_assoc]
      _ = m0 * S.J a (-t + t') * S.e (a+1) := by
          rw [S.triple a ha han, ← S.J_add, ← h5.eq]; simp only [mul_assoc]
  rw [this]
  exact S.T_gen (IsMon.step a m0 _ hm0)

/-- J_(i+1)^w T_i ⊆ U_i. -/
lemma L4 {i : ℕ} (hi : 1 ≤ i) (hin : i < n) {z : A} (hz : z ∈ S.T i) (w r : ℤ) (hw : |w| ≤ r) :
    S.J (i+1) w * z ∈ S.U i r := by
  have := span_map (LinearMap.mulLeft R (S.J (i+1) w)) (Q := S.U i r) ?_ hz
  · simpa using this
  rintro _ ⟨m, hm, rfl⟩
  simp only [LinearMap.mulLeft_apply]
  have h1 : Commute m (S.J (i+1) w) := S.monc hm _ (fun j hj hji =>
    ((show Commute (S.u j : A) (S.u (i+1)) from S.ucomm j (i+1) hj (by omega) (by omega))
      ).units_zpow_right w)
  rw [← mul_assoc, ← h1.eq, mul_assoc, S.m9Lz hi hin, ← mul_assoc]
  exact S.U_gen hm (by rwa [abs_neg])

lemma b1 (i : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    S.x i * S.J i 1 = S.J (i+1) 1 * S.x i - S.δ • S.J (i+1) 1 + S.δ • (S.J (i+1) 1 * S.e i) := by
  have h : S.J (i+1) 1 * S.xi i = S.x i * S.J i 1 := by
    rw [S.J_one, S.J_one, S.urec i hi hin, mul_assoc, S.x_xi i hi hin, mul_one]
  rw [← h, S.xi_eq i hi hin]
  simp only [mul_sub, smul_sub, mul_smul_comm, mul_one]; abel

lemma b3 (a : ℕ) (ha : 1 ≤ a) (han : a < n) :
    S.x a * S.J (a+1) 1 = S.J a 1 * S.x a + S.δ • S.J (a+1) 1 - S.δ • (S.e a * S.J (a+1) 1) := by
  have hxx : S.x a * S.x a = 1 + S.δ • S.x a - S.δ • (S.e a * S.x a) := by
    have h := S.xi_eq a ha han
    have : S.x a = S.xi a + S.δ • (1 - S.e a) := by rw [h]; abel
    conv_lhs => rw [show S.x a * S.x a = S.x a * (S.xi a + S.δ • (1 - S.e a)) by rw [← this]]
    rw [mul_add, S.x_xi a ha han, mul_smul_comm, mul_sub, mul_one, S.xe a ha han, ← S.ex a ha han,
      smul_sub]; abel
  have hv : S.J (a+1) 1 = S.x a * S.J a 1 * S.x a := by
    rw [S.J_one, S.J_one, S.urec a ha han]
  rw [hv, show S.x a * (S.x a * S.J a 1 * S.x a) = (S.x a * S.x a) * (S.J a 1 * S.x a) by
    simp only [mul_assoc], hxx]
  simp only [add_mul, sub_mul, one_mul, smul_mul_assoc, mul_assoc]

end Sys
end X8L25


namespace X8L25

set_option linter.unusedSectionVars false

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {n : ℕ}

namespace Sys
variable (S : Sys R A n)

lemma IIstep (i : ℕ) (hi : 1 ≤ i) (hin : i < n) (p : ℕ)
    (hI : ∀ r : ℕ, r < p → S.e i * S.J i r * S.e i ∈ S.T i) :
    ∀ w : ℕ, S.J (i+1) w * S.x i * S.J i p * S.e i ∈ S.U i (w + p) := by
  induction p with
  | zero =>
    intro w
    rw [Nat.cast_zero, S.J_zero, mul_one, mul_assoc, S.xe i hi hin, mul_smul_comm, S.m9Lz hi hin]
    exact Submodule.smul_mem _ _ (S.U_gen1 hi (by simp))
  | succ p ih =>
    intro w
    have hI' : ∀ r : ℕ, r < p → S.e i * S.J i r * S.e i ∈ S.T i := fun r hr => hI r (by omega)
    have e1 : S.J i ((p+1 : ℕ) : ℤ) = S.J i 1 * S.J i p := by
      rw [← S.J_add]; push_cast; ring_nf
    have e2 : S.J (i+1) ((w+1 : ℕ) : ℤ) = S.J (i+1) w * S.J (i+1) 1 := by
      rw [← S.J_add]; push_cast; ring_nf
    have : S.J (i+1) w * S.x i * S.J i ((p+1 : ℕ) : ℤ) * S.e i =
        S.J (i+1) ((w+1 : ℕ) : ℤ) * S.x i * S.J i p * S.e i -
        S.δ • (S.J (i+1) ((w+1 : ℕ) : ℤ) * S.J i p * S.e i) +
        S.δ • (S.J (i+1) ((w+1 : ℕ) : ℤ) * (S.e i * S.J i p * S.e i)) := by
      rw [e1, e2, show S.J (i+1) w * S.x i * (S.J i 1 * S.J i p) * S.e i =
        S.J (i+1) w * (S.x i * S.J i 1) * S.J i p * S.e i by simp only [mul_assoc], S.b1 i hi hin]
      simp only [mul_sub, mul_add, sub_mul, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    rw [this]
    refine add_mem (sub_mem ?_ (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ ?_)
    · refine S.U_mono i ?_ (ih hI' (w+1)); push_cast; omega
    · rw [← (S.cJJ (m := i+1) hi (by omega) (by omega) (p:ℤ) ((w+1:ℕ):ℤ)).eq, mul_assoc,
        S.m9Lz hi hin, ← mul_assoc, ← S.J_add]
      exact S.U_gen1 hi (by rw [abs_le]; constructor <;> push_cast <;> omega)
    · exact S.L4 hi hin (hI p (by omega)) _ _ (by rw [abs_le]; push_cast; constructor <;> omega)

lemma mainII_of (i : ℕ) (hi : 1 ≤ i) (hin : i < n) (p : ℕ)
    (hI : ∀ r : ℕ, r < p → S.e i * S.J i r * S.e i ∈ S.T i) :
    S.x i * S.J i p * S.e i ∈ S.U i p := by
  simpa [S.J_zero] using S.IIstep i hi hin p hI 0

lemma Fx {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n) (r : ℕ)
    (hIr : S.e (a+1) * S.J (a+1) r * S.e (a+1) ∈ S.T (a+1))
    (hIIr : S.x (a+1) * S.J (a+1) r * S.e (a+1) ∈ S.U (a+1) r) :
    S.e (a+1) * S.x a * S.J (a+1) r * S.e (a+1) ∈ S.T (a+1) := by
  have hfx : S.e (a+1) * S.x a = S.e (a+1) * S.e a * S.xi (a+1) := by
    rw [← S.nearR a ha han, mul_assoc _ (S.x (a+1)), S.x_xi (a+1) (by omega) han, mul_one]
  have : S.e (a+1) * S.x a * S.J (a+1) r * S.e (a+1) =
      S.e (a+1) * S.e a * (S.x (a+1) * S.J (a+1) r * S.e (a+1)) -
      S.δ • (S.e (a+1) * S.e a * (S.J (a+1) r * S.e (a+1))) +
      S.δ • ((S.e (a+1) * S.e a * S.e (a+1)) * S.J (a+1) r * S.e (a+1)) := by
    rw [hfx, S.xi_eq (a+1) (by omega) han]
    simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_one, mul_assoc,
      smul_sub]
    abel
  rw [this, S.triple a ha han]
  refine add_mem (sub_mem (S.L3 ha han hIIr) (Submodule.smul_mem _ _
    (S.L3 ha han (S.U_gen1 (i := a+1) (by omega) (t := r) (r := r) (by simp))))) ?_
  · exact Submodule.smul_mem _ _ hIr

lemma G {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n)
    (hIa : ∀ p : ℕ, S.e a * S.J a p * S.e a ∈ S.T a)
    (hIIa : ∀ p : ℕ, S.x a * S.J a p * S.e a ∈ S.U a p) (q : ℕ)
    (hq : ∀ r : ℕ, r ≤ q → S.e (a+1) * S.J (a+1) r * S.e (a+1) ∈ S.T (a+1)) :
    ∀ q' : ℕ, q' ≤ q → ∀ c : ℕ,
      S.e (a+1) * S.x a * S.J a c * S.x a * S.J (a+1) q' * S.e (a+1) ∈ S.T (a+1) := by
  have hIIq : ∀ r : ℕ, r ≤ q → S.x (a+1) * S.J (a+1) r * S.e (a+1) ∈ S.U (a+1) r :=
    fun r hr => S.mainII_of (a+1) (by omega) han r (fun r' hr' => hq r' (by omega))
  intro q'
  induction q' with
  | zero =>
    intro _ c
    have hxf : S.x a * S.e (a+1) = S.xi (a+1) * (S.e a * S.e (a+1)) := by
      rw [← S.nearL a ha han, ← mul_assoc, ← mul_assoc, S.xi_x (a+1) (by omega) han, one_mul]
    have hfxXi : S.e (a+1) * S.x a * S.xi (a+1) =
        S.e (a+1) * S.e a - S.δ • (S.e (a+1) * S.x a) + (S.δ * S.lami) • S.e (a+1) := by
      rw [S.xi_eq (a+1) (by omega) han, mul_sub, S.nearR a ha han, mul_smul_comm, mul_sub,
        mul_one, S.exe ha han, smul_sub, smul_smul]; abel
    have hc : Commute (S.J a c) (S.xi (a+1)) := S.cxi ha (by omega) han _
    have : S.e (a+1) * S.x a * S.J a c * S.x a * S.J (a+1) ((0:ℕ):ℤ) * S.e (a+1) =
        S.e (a+1) * (S.e a * S.J a c * S.e a) * S.e (a+1) -
        S.δ • (S.e (a+1) * (S.x a * S.J a c * S.e a) * S.e (a+1)) +
        (S.δ * S.lami) • (S.e (a+1) * (S.J a c * S.e a) * S.e (a+1)) := by
      rw [Nat.cast_zero, S.J_zero, mul_one, mul_assoc _ (S.x a), hxf, ← mul_assoc, mul_assoc _ (S.J a c),
        hc.eq, ← mul_assoc, ← mul_assoc, hfxXi]
      simp only [add_mul, sub_mul, smul_mul_assoc, mul_assoc]
    rw [this]
    refine add_mem (sub_mem (S.L1 ha han (S.T_le_U a (le_refl 0) (hIa c)))
      (Submodule.smul_mem _ _ (S.L1 ha han (hIIa c)))) (Submodule.smul_mem _ _ ?_)
    exact S.L1 ha han (S.U_gen1 ha (t := c) (r := c) (by simp))
  | succ q' ih =>
    intro hq' c
    have e1 : S.J (a+1) ((q'+1 : ℕ) : ℤ) = S.J (a+1) 1 * S.J (a+1) q' := by
      rw [← S.J_add]; push_cast; ring_nf
    have e2 : S.J a ((c+1 : ℕ) : ℤ) = S.J a c * S.J a 1 := by
      rw [← S.J_add]; push_cast; ring_nf
    have : S.e (a+1) * S.x a * S.J a c * S.x a * S.J (a+1) ((q'+1 : ℕ) : ℤ) * S.e (a+1) =
        S.e (a+1) * S.x a * S.J a ((c+1 : ℕ) : ℤ) * S.x a * S.J (a+1) q' * S.e (a+1) +
        S.δ • (S.e (a+1) * S.x a * S.J a c * S.J (a+1) ((q'+1 : ℕ) : ℤ) * S.e (a+1)) -
        S.δ • (S.e (a+1) * S.x a * S.J a c * (S.e a * S.J (a+1) ((q'+1 : ℕ) : ℤ)) * S.e (a+1)) := by
      rw [e1, e2, show S.e (a+1) * S.x a * S.J a c * S.x a * (S.J (a+1) 1 * S.J (a+1) q') * S.e (a+1)
        = S.e (a+1) * S.x a * S.J a c * (S.x a * S.J (a+1) 1) * S.J (a+1) q' * S.e (a+1) by
          simp only [mul_assoc], S.b3 a ha (by omega)]
      simp only [mul_sub, mul_add, sub_mul, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    rw [this]
    refine sub_mem (add_mem (ih (by omega) (c+1)) (Submodule.smul_mem _ _ ?_))
      (Submodule.smul_mem _ _ ?_)
    · have hc1 : Commute (S.J a c) (S.J (a+1) ((q'+1 : ℕ) : ℤ)) := S.cJJ ha (by omega) (by omega) _ _
      have hc2 : Commute (S.J a c) (S.e (a+1)) := S.ce ha (by omega) han _
      have : S.e (a+1) * S.x a * S.J a c * S.J (a+1) ((q'+1 : ℕ) : ℤ) * S.e (a+1) =
          S.e (a+1) * S.x a * S.J (a+1) ((q'+1 : ℕ) : ℤ) * S.e (a+1) * S.J a c := by
        rw [mul_assoc _ (S.J a c), hc1.eq, ← mul_assoc, mul_assoc _ (S.J a c), hc2.eq, ← mul_assoc]
      rw [this]
      exact S.L2 ha han (S.Fx ha han _ (hq _ hq') (hIIq _ hq')) _
    · have hc2 : Commute (S.J a (-((q'+1 : ℕ) : ℤ))) (S.e (a+1)) := S.ce ha (by omega) han _
      rw [S.m9Rz ha (by omega)]
      have : S.e (a+1) * S.x a * S.J a c * (S.e a * S.J a (-((q'+1 : ℕ) : ℤ))) * S.e (a+1) =
          S.e (a+1) * (S.x a * S.J a c * S.e a) * S.e (a+1) * S.J a (-((q'+1 : ℕ) : ℤ)) := by
        rw [← mul_assoc, mul_assoc _ (S.J a _), hc2.eq]; simp only [mul_assoc]
      rw [this]
      exact S.L2 ha han (S.L1 ha han (hIIa c)) _

theorem mainI : ∀ i, 1 ≤ i → i < n → ∀ p : ℕ, S.e i * S.J i p * S.e i ∈ S.T i := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro h1 p
    obtain ⟨c, hc⟩ := S.base h1 p
    rw [show S.J 1 p = ↑(S.u 1 ^ (p:ℤ)) from rfl, hc]
    exact Submodule.smul_mem _ _ (by simpa using S.T_gen (IsMon.base (u := S.u)))
  | succ a ha ih =>
    intro han p
    have hIa := ih (by omega)
    have hIIa : ∀ p : ℕ, S.x a * S.J a p * S.e a ∈ S.U a p :=
      fun p => S.mainII_of a ha (by omega) p (fun r _ => hIa r)
    induction p using Nat.strong_induction_on with
    | _ p hp =>
      cases p with
      | zero =>
        obtain ⟨c, hc⟩ := S.sq (a+1) (by omega) han
        rw [Nat.cast_zero, S.J_zero, mul_one, hc]
        exact Submodule.smul_mem _ _ (by simpa using S.T_gen (IsMon.one (u := S.u) (a+1) (by omega)))
      | succ q =>
        have := S.G ha han hIa hIIa q (fun r hr => hp r (by omega)) q le_rfl 1
        rw [Nat.cast_one] at this
        convert this using 1
        rw [show ((q+1:ℕ):ℤ) = 1 + q by push_cast; ring, S.J_add, S.J_one (a+1),
          S.urec a ha (by omega), ← S.J_one a]
        simp only [mul_assoc]

theorem mainII (i : ℕ) (hi : 1 ≤ i) (hin : i < n) (p : ℕ) :
    S.x i * S.J i p * S.e i ∈ S.U i p :=
  S.mainII_of i hi hin p (fun r _ => S.mainI i hi hin r)

end Sys
end X8L25


namespace X8L25

set_option linter.unusedSectionVars false

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {n : ℕ}

open MulOpposite

def opU (w : Aˣ) : (Aᵐᵒᵖ)ˣ :=
  ⟨op (w : A), op (↑w⁻¹ : A), by rw [← op_mul, Units.inv_mul, op_one],
    by rw [← op_mul, Units.mul_inv, op_one]⟩

@[simp] lemma opU_val (w : Aˣ) : (↑(opU w) : Aᵐᵒᵖ) = op (w : A) := rfl

lemma opU_zpow (w : Aˣ) (t : ℤ) : (↑(opU w ^ t) : Aᵐᵒᵖ) = op (↑(w ^ t) : A) := by
  induction t using Int.induction_on with
  | zero => simp
  | succ t ih =>
    rw [zpow_add_one, Units.val_mul, ih, opU_val, ← op_mul, ← Units.val_mul, ← zpow_one_add,
      add_comm]
  | pred t ih =>
    rw [zpow_sub_one, Units.val_mul, ih, show (↑(opU w)⁻¹ : Aᵐᵒᵖ) = op (↑w⁻¹ : A) from rfl,
      ← op_mul, ← Units.val_mul, show (-(t:ℤ) - 1) = -1 + -(t:ℤ) by ring, zpow_add, zpow_neg_one]

namespace Sys
variable (S : Sys R A n)

lemma xie (i : ℕ) (hi : 1 ≤ i) (hin : i < n) : S.xi i * S.e i = S.lami • S.e i := by
  have h := congrArg (S.xi i * ·) (S.xe i hi hin)
  simp only [← mul_assoc, S.xi_x i hi hin, one_mul, mul_smul_comm] at h
  conv_rhs => rw [h]
  rw [smul_smul, S.hlam, one_smul]

lemma exi (i : ℕ) (hi : 1 ≤ i) (hin : i < n) : S.e i * S.xi i = S.lami • S.e i := by
  have h := congrArg (· * S.xi i) (S.ex i hi hin)
  simp only [mul_assoc, S.x_xi i hi hin, mul_one, smul_mul_assoc] at h
  conv_rhs => rw [h]
  rw [smul_smul, S.hlam, one_smul]

lemma nearLi {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n) :
    S.xi (a+1) * S.xi a * S.e (a+1) = S.e a * S.e (a+1) := by
  have h1 : S.xi (a+1) * (S.e a * S.e (a+1)) = S.x a * S.e (a+1) := by
    rw [← S.nearL a ha han, ← mul_assoc, ← mul_assoc, S.xi_x (a+1) (by omega) han, one_mul]
  have h2 : S.xi (a+1) * S.e (a+1) = S.lami • S.e (a+1) := S.xie (a+1) (by omega) han
  have h3 : S.xi (a+1) * (S.x a * S.e (a+1)) =
      S.e a * S.e (a+1) - S.δ • (S.x a * S.e (a+1)) + (S.δ * S.lami) • S.e (a+1) := by
    rw [S.xi_eq (a+1) (by omega) han, sub_mul, ← mul_assoc, S.nearL a ha han, smul_mul_assoc,
      sub_mul, one_mul, ← mul_assoc, S.exe ha han, smul_sub, smul_smul]; abel
  calc S.xi (a+1) * S.xi a * S.e (a+1)
      = S.xi (a+1) * ((S.x a - S.δ • (1 - S.e a)) * S.e (a+1)) := by
        rw [S.xi_eq a ha (by omega), mul_assoc]
    _ = S.xi (a+1) * (S.x a * S.e (a+1)) - S.δ • (S.xi (a+1) * S.e (a+1)) +
        S.δ • (S.xi (a+1) * (S.e a * S.e (a+1))) := by
        simp only [sub_mul, mul_sub, one_mul, smul_mul_assoc, mul_smul_comm, smul_sub]; abel
    _ = S.e a * S.e (a+1) := by
        rw [h1, h2, h3, smul_smul]; abel

lemma nearRi {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n) :
    S.e (a+1) * S.xi a * S.xi (a+1) = S.e (a+1) * S.e a := by
  have h1 : S.e (a+1) * S.e a * S.xi (a+1) = S.e (a+1) * S.x a := by
    rw [← S.nearR a ha han, mul_assoc _ (S.x (a+1)), S.x_xi (a+1) (by omega) han, mul_one]
  have h2 : S.e (a+1) * S.xi (a+1) = S.lami • S.e (a+1) := S.exi (a+1) (by omega) han
  have h3 : S.e (a+1) * S.x a * S.xi (a+1) =
      S.e (a+1) * S.e a - S.δ • (S.e (a+1) * S.x a) + (S.δ * S.lami) • S.e (a+1) := by
    rw [S.xi_eq (a+1) (by omega) han, mul_sub, S.nearR a ha han, mul_smul_comm, mul_sub,
      mul_one, S.exe ha han, smul_sub, smul_smul]; abel
  calc S.e (a+1) * S.xi a * S.xi (a+1)
      = S.e (a+1) * (S.x a - S.δ • (1 - S.e a)) * S.xi (a+1) := by
        rw [S.xi_eq a ha (by omega)]
    _ = S.e (a+1) * S.x a * S.xi (a+1) - S.δ • (S.e (a+1) * S.xi (a+1)) +
        S.δ • (S.e (a+1) * S.e a * S.xi (a+1)) := by
        simp only [sub_mul, mul_sub, mul_one, smul_mul_assoc, mul_smul_comm, smul_sub, mul_assoc]
        abel
    _ = S.e (a+1) * S.e a := by
        rw [h1, h2, h3, smul_smul]; abel

lemma ureci {a : ℕ} (ha : 1 ≤ a) (han : a < n) :
    (↑(S.u (a+1))⁻¹ : A) = S.xi a * ↑(S.u a)⁻¹ * S.xi a := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [S.urec a ha han]
  calc S.x a * ↑(S.u a) * S.x a * (S.xi a * ↑(S.u a)⁻¹ * S.xi a)
      = S.x a * ↑(S.u a) * (S.x a * S.xi a) * ↑(S.u a)⁻¹ * S.xi a := by simp only [mul_assoc]
    _ = 1 := by
      rw [S.x_xi a ha han, mul_one, mul_assoc (S.x a), Units.mul_inv, mul_one, S.x_xi a ha han]

lemma Jinv (i : ℕ) : (↑(S.u i)⁻¹ : A) = S.J i (-1) := by simp [J]

def mirror : Sys R A n where
  δ := -S.δ
  lam := S.lami
  lami := S.lam
  hlam := by rw [mul_comm]; exact S.hlam
  x := S.xi
  xi := S.x
  e := S.e
  u := fun i => (S.u i)⁻¹
  x_xi := S.xi_x
  xi_x := S.x_xi
  skein := fun i hi hin => by rw [← neg_sub, S.skein i hi hin, neg_smul]
  xe := fun i hi hin => S.xie i hi hin
  ex := fun i hi hin => S.exi i hi hin
  sq := S.sq
  nearL := fun a ha han => S.nearLi ha han
  nearR := fun a ha han => S.nearRi ha han
  triple := S.triple
  urec := fun a ha han => S.ureci ha han
  m9L := fun a ha han => by
    rw [S.Jinv, S.Jinv, mul_assoc, S.m9Lz ha han, ← mul_assoc, ← S.J_add]; simp [S.J_zero]
  m9R := fun a ha han => by
    rw [S.Jinv, S.Jinv, mul_assoc, (S.cJJ (m := a+1) ha (by omega) (by omega) (-1) (-1)).eq,
      ← mul_assoc, S.m9Rz ha han, mul_assoc, ← S.J_add]; simp [S.J_zero]
  ucomm := fun j m hj hjm hm => by
    have := congrArg Units.val (S.uc hj hjm hm).inv_inv.eq
    simpa using this
  ux := fun j m hj hjm hm => ((S.cxi1 hj hjm hm).units_inv_left).eq
  ue := fun j m hj hjm hm =>
    ((show Commute (S.u j : A) (S.e m) from S.ue j m hj hjm hm).units_inv_left).eq
  base := fun h p => by simpa [inv_zpow'] using S.base h (-p)

lemma mirror_J (i : ℕ) (t : ℤ) : S.mirror.J i t = S.J i (-t) := by
  show (↑((S.u i)⁻¹ ^ t) : A) = ↑(S.u i ^ (-t)); rw [inv_zpow']

lemma T_mirror_le (i : ℕ) : S.mirror.T i ≤ S.T i := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, hm, rfl⟩
  exact S.T_gen (IsMon.of_inv hm)

lemma U_mirror_le (i : ℕ) (r : ℤ) : S.mirror.U i r ≤ S.U i r := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, t, hm, ht, rfl⟩
  rw [S.mirror_J]
  exact S.U_gen (IsMon.of_inv hm) (by rwa [abs_neg])

theorem allI (i : ℕ) (hi : 1 ≤ i) (hin : i < n) (p : ℤ) :
    S.e i * S.J i p * S.e i ∈ S.T i := by
  rcases le_or_gt 0 p with hp | hp
  · have := S.mainI i hi hin p.toNat
    rwa [Int.toNat_of_nonneg hp] at this
  · have := S.mirror.mainI i hi hin (-p).toNat
    rw [S.mirror_J, Int.toNat_of_nonneg (by omega), neg_neg] at this
    exact S.T_mirror_le i this

theorem allII (i : ℕ) (hi : 1 ≤ i) (hin : i < n) (p : ℤ) :
    S.x i * S.J i p * S.e i ∈ S.U i |p| := by
  rcases le_or_gt 0 p with hp | hp
  · have := S.mainII i hi hin p.toNat
    rw [Int.toNat_of_nonneg hp] at this
    rwa [abs_of_nonneg hp]
  · have h := S.mirror.mainII i hi hin (-p).toNat
    rw [S.mirror_J, Int.toNat_of_nonneg (by omega), neg_neg, ← abs_of_neg hp] at h
    have h' : S.xi i * S.J i p * S.e i ∈ S.U i |p| := S.U_mirror_le i _ h
    have : S.x i * S.J i p * S.e i = S.xi i * S.J i p * S.e i + S.δ • (S.J i p * S.e i) -
        S.δ • (S.e i * S.J i p * S.e i) := by
      rw [show S.x i = S.xi i + S.δ • (1 - S.e i) by rw [S.xi_eq i hi hin]; abel]
      simp only [add_mul, sub_mul, one_mul, smul_mul_assoc, smul_sub, mul_assoc]
      abel
    rw [this]
    exact sub_mem (add_mem h' (Submodule.smul_mem _ _ (S.U_gen1 hi le_rfl)))
      (Submodule.smul_mem _ _ (S.T_le_U i (abs_nonneg p) (S.allI i hi hin p)))

end Sys
end X8L25


namespace X8L25

set_option linter.unusedSectionVars false

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {n : ℕ}

open MulOpposite

namespace Sys
variable (S : Sys R A n)

def opS : Sys R Aᵐᵒᵖ n where
  δ := S.δ
  lam := S.lam
  lami := S.lami
  hlam := S.hlam
  x := fun i => op (S.x i)
  xi := fun i => op (S.xi i)
  e := fun i => op (S.e i)
  u := fun i => opU (S.u i)
  x_xi := fun i hi hin => by
    apply unop_injective; simp [S.xi_x i hi hin]
  xi_x := fun i hi hin => by
    apply unop_injective; simp [S.x_xi i hi hin]
  skein := fun i hi hin => by
    apply unop_injective; simp [S.skein i hi hin]
  xe := fun i hi hin => by
    apply unop_injective; simp [S.ex i hi hin]
  ex := fun i hi hin => by
    apply unop_injective; simp [S.xe i hi hin]
  sq := fun i hi hin => by
    obtain ⟨c, hc⟩ := S.sq i hi hin
    exact ⟨c, by apply unop_injective; simp [hc]⟩
  nearL := fun a ha han => by
    apply unop_injective; simp only [unop_mul, unop_op]; simpa only [mul_assoc] using S.nearR a ha han
  nearR := fun a ha han => by
    apply unop_injective; simp only [unop_mul, unop_op]
    simpa only [mul_assoc] using S.nearL a ha han
  triple := fun a ha han => by
    apply unop_injective; simp only [unop_mul, unop_op]
    simpa only [mul_assoc] using S.triple a ha han
  urec := fun a ha han => by
    apply unop_injective; simp only [opU_val, unop_mul, unop_op]
    rw [S.urec a ha han, mul_assoc]
  m9L := fun a ha han => by
    apply unop_injective; simp only [opU_val, unop_mul, unop_op]
    rw [← S.ucomm a (a+1) ha (by omega) (by omega), ← mul_assoc, S.m9R a ha han]
  m9R := fun a ha han => by
    apply unop_injective; simp only [opU_val, unop_mul, unop_op]
    rw [← mul_assoc, ← S.ucomm a (a+1) ha (by omega) (by omega), S.m9L a ha han]
  ucomm := fun j m hj hjm hm => by
    apply unop_injective; simp only [opU_val, unop_mul, unop_op]
    exact (S.ucomm j m hj hjm hm).symm
  ux := fun j m hj hjm hm => by
    apply unop_injective; simp only [opU_val, unop_mul, unop_op]
    exact (S.ux j m hj hjm hm).symm
  ue := fun j m hj hjm hm => by
    apply unop_injective; simp only [opU_val, unop_mul, unop_op]
    exact (S.ue j m hj hjm hm).symm
  base := fun h p => by
    obtain ⟨c, hc⟩ := S.base h p
    refine ⟨c, ?_⟩
    apply unop_injective; simp only [opU_zpow, unop_mul, unop_op, unop_smul]
    rw [← mul_assoc, hc]

lemma opS_J (i : ℕ) (t : ℤ) : S.opS.J i t = op (S.J i t) := opU_zpow _ _

lemma isMon_op {i : ℕ} {m' : Aᵐᵒᵖ} (h : IsMon S.opS.u i m') (hin : i ≤ n) :
    ∃ m, IsMon S.u i m ∧ m' = op m := by
  induction h with
  | base => exact ⟨1, IsMon.base, rfl⟩
  | step i m' t h ih =>
    obtain ⟨m, hm, rfl⟩ := ih (by omega)
    refine ⟨m * ↑(S.u i ^ t), IsMon.step i m t hm, ?_⟩
    have hc : Commute m (S.J i t) := S.monc hm _ (fun j hj hji =>
      ((show Commute (S.u j : A) (S.u i) from S.ucomm j i hj hji (by omega))).units_zpow_right t)
    show op m * S.opS.J i t = _
    rw [S.opS_J, ← op_mul, ← hc.eq]; rfl

def V (i : ℕ) (r : ℤ) : Submodule R A :=
  Submodule.span R {z | ∃ m, ∃ t : ℤ, IsMon S.u i m ∧ |t| ≤ r ∧ z = S.e i * (m * S.J i t)}

lemma V_gen {i : ℕ} {m : A} {t r : ℤ} (h : IsMon S.u i m) (ht : |t| ≤ r) :
    S.e i * (m * S.J i t) ∈ S.V i r :=
  Submodule.subset_span ⟨m, t, h, ht, rfl⟩

lemma U_op_le (i : ℕ) (hin : i ≤ n) (r : ℤ) {y : Aᵐᵒᵖ} (hy : y ∈ S.opS.U i r) :
    unop y ∈ S.V i r := by
  have := span_map (MulOpposite.opLinearEquiv R (M := A)).symm.toLinearMap (Q := S.V i r) ?_ hy
  · simpa using this
  rintro _ ⟨m', t, hm', ht, rfl⟩
  obtain ⟨m, hm, rfl⟩ := S.isMon_op hm' hin
  have hc : Commute m (S.J i t) := S.monc hm _ (fun j hj hji =>
    ((show Commute (S.u j : A) (S.u i) from S.ucomm j i hj hji (by omega))).units_zpow_right t)
  simp only [LinearEquiv.coe_toLinearMap, MulOpposite.coe_opLinearEquiv_symm]
  show unop (op m * S.opS.J i t * op (S.e i)) ∈ _
  rw [S.opS_J]
  simp only [unop_mul, unop_op]
  rw [← hc.eq]
  exact Submodule.subset_span ⟨m, t, hm, ht, rfl⟩

lemma T_le_V (i : ℕ) (hi : 1 ≤ i) (hin : i < n) {r : ℤ} (hr : 0 ≤ r) : S.T i ≤ S.V i r := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, hm, rfl⟩
  have hc : Commute m (S.e i) := S.monc hm _ (fun j hj hji => S.ue j i hj hji hin)
  rw [hc.eq]
  have := S.V_gen hm (t := 0) (r := r) (by simpa using hr)
  simpa [S.J_zero] using this

theorem allIII (i : ℕ) (hi : 1 ≤ i) (hin : i < n) (p : ℤ) :
    S.e i * S.J i p * S.x i ∈ S.V i |p| := by
  have h0 := S.opS.allII i hi hin p
  rcases le_or_gt 0 p with hp | hp
  · have := S.U_op_le i hin.le _ h0
    rw [S.opS_J] at this
    simpa [mul_assoc, opS] using this
  · -- use the mirror of the op system to get xi, then convert
    have h1 := S.opS.mirror.mainII i hi hin (-p).toNat
    rw [S.opS.mirror_J, Int.toNat_of_nonneg (by omega), neg_neg, ← abs_of_neg hp] at h1
    have h2 := S.U_op_le i hin.le _ (S.opS.U_mirror_le i _ h1)
    rw [S.opS_J] at h2
    have h2' : S.e i * S.J i p * S.xi i ∈ S.V i |p| := by
      simpa [mul_assoc, opS, mirror] using h2
    have : S.e i * S.J i p * S.x i = S.e i * S.J i p * S.xi i + S.δ • (S.e i * S.J i p) -
        S.δ • (S.e i * S.J i p * S.e i) := by
      rw [show S.x i = S.xi i + S.δ • (1 - S.e i) by rw [S.xi_eq i hi hin]; abel]
      simp only [mul_add, mul_sub, mul_one, mul_smul_comm, smul_sub, mul_assoc]
      abel
    rw [this]
    have h3 : S.e i * S.J i p ∈ S.V i |p| := by
      simpa using S.V_gen (IsMon.one i hi) (t := p) (r := |p|) le_rfl
    exact sub_mem (add_mem h2' (Submodule.smul_mem _ _ h3))
      (Submodule.smul_mem _ _ (S.T_le_V i hi hin (abs_nonneg p) (S.allI i hi hin p)))

end Sys
end X8L25

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L25C

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

lemma rel {a b : FreeAlgebra R (CyclotomicLetter n)} (h : NonsplitBMWRel P n a b) :
    presentationMap P n a = presentationMap P n b :=
  RingQuot.mkAlgHom_rel R h

lemma x_xi (i : ℕ) (hi : 1 ≤ i ∧ i < n) : X P n i false * X P n i true = 1 := by
  have := rel P n (NonsplitBMWRel.invL i hi); simpa [X, map_mul] using this

lemma xi_x (i : ℕ) (hi : 1 ≤ i ∧ i < n) : X P n i true * X P n i false = 1 := by
  have := rel P n (NonsplitBMWRel.invR i hi); simpa [X, map_mul] using this

lemma nearL (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 = j ∨ j + 1 = i) :
    X P n i false * X P n j false * E P n i = E P n j * E P n i := by
  have := rel P n (NonsplitBMWRel.nearL i j hi hj hd); simpa [X, E, map_mul] using this

lemma nearR (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 = j ∨ j + 1 = i) :
    E P n j * X P n i false * X P n j false = E P n j * E P n i := by
  have := rel P n (NonsplitBMWRel.nearR i j hi hj hd); simpa [X, E, map_mul] using this

lemma tripleE (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 = j ∨ j + 1 = i) :
    E P n i * E P n j * E P n i = E P n i := by
  have := rel P n (NonsplitBMWRel.tripleE i j hi hj hd); simpa [E, map_mul] using this

lemma xeFar (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 < j ∨ j + 1 < i) :
    X P n i false * E P n j = E P n j * X P n i false := by
  have := rel P n (NonsplitBMWRel.xeFar i j hi hj hd); simpa [X, E, map_mul] using this

lemma xFar (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 < j ∨ j + 1 < i) :
    X P n i false * X P n j false = X P n j false * X P n i false := by
  have := rel P n (NonsplitBMWRel.xFar i j hi hj hd); simpa [X, map_mul] using this

lemma braid (i : ℕ) (hi : 1 ≤ i ∧ i + 1 < n) :
    X P n i false * X P n (i+1) false * X P n i false =
      X P n (i+1) false * X P n i false * X P n (i+1) false := by
  have := rel P n (NonsplitBMWRel.braid i hi); simpa [X, map_mul] using this

lemma ye (i : ℕ) (hi : 1 < i ∧ i < n) : Y P n false * E P n i = E P n i * Y P n false := by
  have := rel P n (NonsplitBMWRel.ye i hi); simpa [Y, E, map_mul] using this

lemma yx (i : ℕ) (hi : 1 < i ∧ i < n) : Y P n false * X P n i false = X P n i false * Y P n false := by
  have := rel P n (NonsplitBMWRel.yx i hi); simpa [Y, X, map_mul] using this

lemma skein (i : ℕ) (hi : 1 ≤ i ∧ i < n) :
    X P n i false - X P n i true = skeinDelta P • (1 - E P n i) := by
  have h := rel P n (NonsplitBMWRel.skein i hi)
  simp only [map_sub, map_mul, map_one, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

lemma xe (i : ℕ) (hi : 1 ≤ i ∧ i < n) : X P n i false * E P n i = (P.lam : R) • E P n i := by
  have h := rel P n (NonsplitBMWRel.xe i hi)
  simp only [map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

lemma ex (i : ℕ) (hi : 1 ≤ i ∧ i < n) : E P n i * X P n i false = (P.lam : R) • E P n i := by
  have h := rel P n (NonsplitBMWRel.ex i hi)
  simp only [map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

lemma sqE (i : ℕ) (hi : 1 ≤ i ∧ i < n) : E P n i * E P n i = loopZero P • E P n i := by
  have h := rel P n (NonsplitBMWRel.squareE i hi)
  simp only [map_pow, map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def, ← pow_two]; exact h

lemma affine (hn : 2 ≤ n) :
    X P n 1 false * Y P n false * X P n 1 false * Y P n false =
      Y P n false * X P n 1 false * Y P n false * X P n 1 false := by
  have := rel P n (NonsplitBMWRel.affine hn); simpa [X, Y, map_mul] using this

lemma unwrapL (hn : 2 ≤ n) :
    Y P n false * X P n 1 false * Y P n false * E P n 1 = (↑P.lam⁻¹ : R) • E P n 1 := by
  have h := rel P n (NonsplitBMWRel.unwrapL hn)
  simp only [map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

lemma unwrapR (hn : 2 ≤ n) :
    E P n 1 * Y P n false * X P n 1 false * Y P n false = (↑P.lam⁻¹ : R) • E P n 1 := by
  have h := rel P n (NonsplitBMWRel.unwrapR hn)
  simp only [map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

lemma yinv1 (hn : 0 < n) : Y P n false * Y P n true = 1 := by
  have := rel P n (NonsplitBMWRel.yInvL hn); simpa [Y, map_mul] using this

lemma yinv2 (hn : 0 < n) : Y P n true * Y P n false = 1 := by
  have := rel P n (NonsplitBMWRel.yInvR hn); simpa [Y, map_mul] using this

lemma cyc (hn : 0 < n) :
    Y P n false ^ k = ∑ j : Fin k, P.coeff j • Y P n false ^ j.val := by
  have h := rel P n (NonsplitBMWRel.cyclotomic hn)
  simp only [map_pow, map_sum, map_mul, AlgHom.commutes] at h
  simp only [Algebra.smul_def]; exact h

lemma loopr (m : Fin k) (hn : 2 ≤ n) :
    E P n 1 * Y P n false ^ m.val * E P n 1 = P.loop m • E P n 1 := by
  have h := rel P n (NonsplitBMWRel.loop m hn)
  simp only [map_pow, map_mul, AlgHom.commutes] at h
  rw [Algebra.smul_def]; exact h

end X8L25C
end QAlgorithms.Papers.Independent.Gap48.P01



namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L25C

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

lemma JM_succ (inv : Bool) (i : ℕ) (hi : 1 ≤ i) :
    JM P n inv (i+1) = X P n i inv * JM P n inv i * X P n i inv := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rfl

lemma jm_inv (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    JM P n false i * JM P n true i = 1 ∧ JM P n true i * JM P n false i = 1 := by
  induction i, hi using Nat.le_induction with
  | base => exact ⟨yinv1 P n (by omega), yinv2 P n (by omega)⟩
  | succ i hi ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [JM_succ P n false i hi, JM_succ P n true i hi]
    have a1 := x_xi P n i ⟨hi, by omega⟩
    have a2 := xi_x P n i ⟨hi, by omega⟩
    constructor
    · calc X P n i false * JM P n false i * X P n i false * (X P n i true * JM P n true i * X P n i true)
          = X P n i false * JM P n false i * (X P n i false * X P n i true) * JM P n true i * X P n i true := by
            simp only [mul_assoc]
        _ = 1 := by rw [a1, mul_one, mul_assoc (X P n i false), h1, mul_one, a1]
    · calc X P n i true * JM P n true i * X P n i true * (X P n i false * JM P n false i * X P n i false)
          = X P n i true * JM P n true i * (X P n i true * X P n i false) * JM P n false i * X P n i false := by
            simp only [mul_assoc]
        _ = 1 := by rw [a2, mul_one, mul_assoc (X P n i true), h2, mul_one, a2]

lemma jx_comm (j : ℕ) (hj : 1 ≤ j) : ∀ m, j + 1 ≤ m → m < n →
    JM P n false j * X P n m false = X P n m false * JM P n false j := by
  induction j, hj using Nat.le_induction with
  | base => intro m hm hmn; exact yx P n m ⟨by omega, hmn⟩
  | succ j hj ih =>
    intro m hm hmn
    have h1 := ih m (by omega) hmn
    have h2 := xFar P n j m ⟨hj, by omega⟩ ⟨by omega, hmn⟩ (Or.inl (by omega))
    rw [JM_succ P n false j hj]
    exact ((Commute.mul_left (Commute.mul_left h2 h1) h2) : Commute _ _).eq

lemma je_comm (j : ℕ) (hj : 1 ≤ j) : ∀ m, j + 1 ≤ m → m < n →
    JM P n false j * E P n m = E P n m * JM P n false j := by
  induction j, hj using Nat.le_induction with
  | base => intro m hm hmn; exact ye P n m ⟨by omega, hmn⟩
  | succ j hj ih =>
    intro m hm hmn
    have h1 := ih m (by omega) hmn
    have h2 := xeFar P n j m ⟨hj, by omega⟩ ⟨by omega, hmn⟩ (Or.inl (by omega))
    rw [JM_succ P n false j hj]
    exact ((Commute.mul_left (Commute.mul_left h2 h1) h2) : Commute _ _).eq

lemma jj_succ (j : ℕ) (hj : 1 ≤ j) (hjn : j + 1 ≤ n) :
    JM P n false j * JM P n false (j+1) = JM P n false (j+1) * JM P n false j := by
  induction j, hj using Nat.le_induction with
  | base =>
    rw [JM_succ P n false 1 le_rfl]
    show Y P n false * (X P n 1 false * Y P n false * X P n 1 false) =
      X P n 1 false * Y P n false * X P n 1 false * Y P n false
    have := (affine P n (by omega)).symm
    simpa only [mul_assoc] using this
  | succ j hj ih =>
    have ih := ih (by omega)
    rw [JM_succ P n false (j+1) (by omega), JM_succ P n false j hj] at *
    set a := X P n j false
    set b := X P n (j+1) false
    set c := JM P n false j
    have br0 : a * (b * a) = b * (a * b) := by
      have := braid P n j ⟨hj, by omega⟩; simpa only [mul_assoc] using this
    have br : ∀ z, a * (b * (a * z)) = b * (a * (b * z)) := by
      intro z; rw [← mul_assoc b, ← mul_assoc a, br0, mul_assoc, mul_assoc]
    have cb : ∀ z, c * (b * z) = b * (c * z) := by
      intro z; rw [← mul_assoc, jx_comm P n j hj (j+1) le_rfl (by omega), mul_assoc]
    have ih' : ∀ z, c * (a * (c * (a * z))) = a * (c * (a * (c * z))) := by
      intro z; have := congrArg (· * z) ih; simpa only [mul_assoc] using this
    simp only [mul_assoc]
    conv_lhs => rw [br (c * (a * b)), cb (a * (b * (c * (a * b)))), ← cb (a * b), ← br0,
      ih' (b * a), br (c * (a * (c * (b * a))))]
    conv_rhs => rw [br (c * a), cb (a * (b * (c * a))), ← cb a]

lemma jj_comm (j : ℕ) (hj : 1 ≤ j) : ∀ m, j < m → m ≤ n →
    JM P n false j * JM P n false m = JM P n false m * JM P n false j := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => intro h; exact jj_succ P n j hj h
  | succ m hm ih =>
    intro hmn
    have h1 : Commute (JM P n false j) (JM P n false m) := ih (by omega)
    have h2 : Commute (JM P n false j) (X P n m false) := jx_comm P n j hj m hm (by omega)
    rw [JM_succ P n false m (by omega)]
    exact ((h2.mul_right h1).mul_right h2).eq

lemma p1dL (a : ℕ) (ha : 1 ≤ a) (han : a < n) :
    JM P n false a * X P n a false * JM P n false a * E P n a = (↑P.lam⁻¹ : R) • E P n a := by
  induction a, ha using Nat.le_induction with
  | base => exact unwrapL P n (by omega)
  | succ a ha ih =>
    have ih := ih (by omega)
    rw [JM_succ P n false a ha]
    set x := X P n a false
    set b := X P n (a+1) false
    set c := JM P n false a
    set e := E P n a
    set f := E P n (a+1)
    have br0 : x * (b * x) = b * (x * b) := by
      have := braid P n a ⟨ha, han⟩; simpa only [mul_assoc] using this
    have br : ∀ z, x * (b * (x * z)) = b * (x * (b * z)) := by
      intro z; rw [← mul_assoc b, ← mul_assoc x, br0, mul_assoc, mul_assoc]
    have cb : ∀ z, c * (b * z) = b * (c * z) := by
      intro z; rw [← mul_assoc, jx_comm P n a ha (a+1) le_rfl han, mul_assoc]
    have nl1 : b * (x * f) = e * f := by
      have := nearL P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl)
      simpa only [mul_assoc] using this
    have nl2 : x * (b * (e * f)) = f * (e * f) := by
      have := nearL P n a (a+1) ⟨ha, by omega⟩ ⟨by omega, han⟩ (Or.inl rfl)
      have := congrArg (· * f) this; simpa only [mul_assoc] using this
    have tr : f * (e * f) = f := by
      have := tripleE P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl)
      simpa only [mul_assoc] using this
    have ih' : c * (x * (c * (e * f))) = (↑P.lam⁻¹ : R) • (e * f) := by
      have := congrArg (· * f) ih; simpa only [mul_assoc, smul_mul_assoc] using this
    simp only [mul_assoc]
    rw [br (c * (x * f)), cb (x * (b * (c * (x * f)))), ← cb (x * f), nl1, ih',
      mul_smul_comm, mul_smul_comm, nl2, tr]

lemma p1dR (a : ℕ) (ha : 1 ≤ a) (han : a < n) :
    E P n a * JM P n false a * X P n a false * JM P n false a = (↑P.lam⁻¹ : R) • E P n a := by
  induction a, ha using Nat.le_induction with
  | base => exact unwrapR P n (by omega)
  | succ a ha ih =>
    have ih := ih (by omega)
    rw [JM_succ P n false a ha]
    set x := X P n a false
    set b := X P n (a+1) false
    set c := JM P n false a
    set e := E P n a
    set f := E P n (a+1)
    have br0 : x * (b * x) = b * (x * b) := by
      have := braid P n a ⟨ha, han⟩; simpa only [mul_assoc] using this
    have br : ∀ z, x * (b * (x * z)) = b * (x * (b * z)) := by
      intro z; rw [← mul_assoc b, ← mul_assoc x, br0, mul_assoc, mul_assoc]
    have cb : ∀ z, c * (b * z) = b * (c * z) := by
      intro z; rw [← mul_assoc, jx_comm P n a ha (a+1) le_rfl han, mul_assoc]
    have nr1 : ∀ z, f * (x * (b * z)) = f * (e * z) := by
      intro z
      have := nearR P n a (a+1) ⟨ha, by omega⟩ ⟨by omega, han⟩ (Or.inl rfl)
      have := congrArg (· * z) this; simpa only [mul_assoc] using this
    have nr2 : e * (b * x) = e * f := by
      have := nearR P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl)
      simpa only [mul_assoc] using this
    have tr : f * (e * f) = f := by
      have := tripleE P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl)
      simpa only [mul_assoc] using this
    have ih' : ∀ z, e * (c * (x * (c * z))) = (↑P.lam⁻¹ : R) • (e * z) := by
      intro z; have := congrArg (· * z) ih; simpa only [mul_assoc, smul_mul_assoc] using this
    simp only [mul_assoc]
    rw [br (c * x), cb (x * (b * (c * x))), ← cb x, nr1, ih', mul_smul_comm, nr2, tr]

end X8L25C
end QAlgorithms.Papers.Independent.Gap48.P01



namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L25C

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

def uU (i : ℕ) : (NonsplitBMW P n)ˣ :=
  if h : 1 ≤ i ∧ i ≤ n then
    ⟨JM P n false i, JM P n true i, (jm_inv P n i h.1 h.2).1, (jm_inv P n i h.1 h.2).2⟩
  else 1

lemma uU_val (i : ℕ) (h : 1 ≤ i ∧ i ≤ n) : (uU P n i : NonsplitBMW P n) = JM P n false i := by
  simp [uU, h]

lemma uU_inv_val (i : ℕ) (h : 1 ≤ i ∧ i ≤ n) :
    (↑(uU P n i)⁻¹ : NonsplitBMW P n) = JM P n true i := by
  simp [uU, h]

lemma uU_val_any (i : ℕ) (h : ¬ (1 ≤ i ∧ i ≤ n)) : (uU P n i : NonsplitBMW P n) = 1 := by
  simp [uU, h]

/-- Every integer power of Y lies in the span of Y^m, m < k. -/
lemma ypow (hn : 0 < n) (p : ℤ) :
    (↑(uU P n 1 ^ p) : NonsplitBMW P n) ∈
      Submodule.span R (Set.range fun m : Fin k => Y P n false ^ m.val) := by
  set W := Submodule.span R (Set.range fun m : Fin k => Y P n false ^ m.val)
  have hgen : ∀ m, m < k → Y P n false ^ m ∈ W := fun m hm =>
    Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩
  have hv : (uU P n 1 : NonsplitBMW P n) = Y P n false := uU_val P n 1 ⟨le_rfl, hn⟩
  have hvi : (↑(uU P n 1)⁻¹ : NonsplitBMW P n) = Y P n true := uU_inv_val P n 1 ⟨le_rfl, hn⟩
  have hYk : Y P n false ^ k ∈ W := by
    rw [cyc P n hn]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hgen j.val j.isLt))
  have hY : ∀ w ∈ W, Y P n false * w ∈ W := by
    intro w hw
    refine X8L25.span_map (LinearMap.mulLeft R (Y P n false)) (Q := W) ?_ hw
    rintro _ ⟨⟨m, hm⟩, rfl⟩
    simp only [LinearMap.mulLeft_apply, ← pow_succ']
    rcases Nat.lt_or_ge (m+1) k with h | h
    · exact hgen _ h
    · obtain rfl : m + 1 = k := by omega
      exact hYk
  have hYinv : Y P n true ∈ W := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := P.positive; omega⟩
    have hc := cyc P n hn
    rw [Fin.sum_univ_succ] at hc
    have hc0 : P.coeff 0 = (P.constant : R) := by
      rw [← P.constant_eq]; rfl
    set w0 := Y P n false ^ k' - ∑ j : Fin k', P.coeff j.succ • Y P n false ^ j.val with hw0
    have h1 : Y P n false * w0 = (P.constant : R) • (1 : NonsplitBMW P n) := by
      rw [hw0, mul_sub, ← pow_succ', hc, Finset.mul_sum, hc0]
      simp only [Fin.val_zero, pow_zero, Fin.val_succ, mul_smul_comm, ← pow_succ']
      abel
    have h2 : w0 = (P.constant : R) • Y P n true := by
      have := congrArg (Y P n true * ·) h1
      simp only [← mul_assoc, yinv2 P n hn, one_mul, mul_smul_comm, mul_one] at this
      exact this
    have h3 : Y P n true = (↑P.constant⁻¹ : R) • w0 := by
      rw [h2, smul_smul, Units.inv_mul, one_smul]
    rw [h3]
    refine Submodule.smul_mem _ _ (sub_mem (hgen _ (by omega)) ?_)
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hgen _ (by omega)))
  have hYi : ∀ w ∈ W, Y P n true * w ∈ W := by
    intro w hw
    refine X8L25.span_map (LinearMap.mulLeft R (Y P n true)) (Q := W) ?_ hw
    rintro _ ⟨⟨m, hm⟩, rfl⟩
    simp only [LinearMap.mulLeft_apply]
    rcases m with _ | m
    · simpa using hYinv
    · rw [pow_succ', ← mul_assoc, yinv2 P n hn, one_mul]
      exact hgen _ (by omega)
  induction p using Int.induction_on with
  | zero => simpa using hgen 0 P.positive
  | succ t ih =>
    rw [show (t:ℤ) + 1 = 1 + t by ring, zpow_add, zpow_one, Units.val_mul, hv]
    exact hY _ ih
  | pred t ih =>
    rw [show (-(t:ℤ) - 1) = -1 + -(t:ℤ) by ring, zpow_add, zpow_neg_one, Units.val_mul, hvi]
    exact hYi _ ih

lemma ybase (hn : 1 < n) (p : ℤ) :
    ∃ c : R, E P n 1 * ↑(uU P n 1 ^ p) * E P n 1 = c • E P n 1 := by
  have hw := ypow P n (by omega) p
  have : E P n 1 * (↑(uU P n 1 ^ p) * E P n 1) ∈ Submodule.span R {E P n 1} := by
    refine X8L25.span_map (LinearMap.mulLeft R (E P n 1) ∘ₗ LinearMap.mulRight R (E P n 1))
      (Q := Submodule.span R {E P n 1}) ?_ hw
    rintro _ ⟨m, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      ← mul_assoc, loopr P n m (by omega)]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
  exact ⟨c, by rw [mul_assoc, ← hc]⟩

def sysOf : X8L25.Sys R (NonsplitBMW P n) n where
  δ := skeinDelta P
  lam := (P.lam : R)
  lami := (↑P.lam⁻¹ : R)
  hlam := by simp
  x := fun i => X P n i false
  xi := fun i => X P n i true
  e := E P n
  u := uU P n
  x_xi := fun i hi hin => x_xi P n i ⟨hi, hin⟩
  xi_x := fun i hi hin => xi_x P n i ⟨hi, hin⟩
  skein := fun i hi hin => skein P n i ⟨hi, hin⟩
  xe := fun i hi hin => xe P n i ⟨hi, hin⟩
  ex := fun i hi hin => ex P n i ⟨hi, hin⟩
  sq := fun i hi hin => ⟨loopZero P, sqE P n i ⟨hi, hin⟩⟩
  nearL := fun a ha han => nearL P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl)
  nearR := fun a ha han => nearR P n a (a+1) ⟨ha, by omega⟩ ⟨by omega, han⟩ (Or.inl rfl)
  triple := fun a ha han => tripleE P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl)
  urec := fun a ha han => by
    rw [uU_val P n (a+1) ⟨by omega, han⟩, uU_val P n a ⟨ha, by omega⟩, JM_succ P n false a ha]
  m9L := fun a ha han => by
    rw [uU_val P n (a+1) ⟨by omega, han⟩, uU_val P n a ⟨ha, by omega⟩, JM_succ P n false a ha]
    have p := p1dL P n a ha han
    simp only [mul_assoc] at p ⊢
    rw [xe P n a ⟨ha, han⟩, mul_smul_comm, mul_smul_comm, mul_smul_comm, p, smul_smul,
      Units.mul_inv, one_smul]
  m9R := fun a ha han => by
    rw [uU_val P n (a+1) ⟨by omega, han⟩, uU_val P n a ⟨ha, by omega⟩, JM_succ P n false a ha]
    have p := congrArg (· * X P n a false) (p1dR P n a ha han)
    simp only [mul_assoc, smul_mul_assoc] at p ⊢
    rw [p, ex P n a ⟨ha, han⟩, smul_smul, Units.inv_mul, one_smul]
  ucomm := fun j m hj hjm hm => by
    rw [uU_val P n j ⟨hj, by omega⟩, uU_val P n m ⟨by omega, hm⟩]
    exact jj_comm P n j hj m hjm hm
  ux := fun j m hj hjm hm => by
    rw [uU_val P n j ⟨hj, by omega⟩]; exact jx_comm P n j hj m hjm hm
  ue := fun j m hj hjm hm => by
    rw [uU_val P n j ⟨hj, by omega⟩]; exact je_comm P n j hj m hjm hm
  base := fun h p => ybase P n h p

lemma JPower_eq (i : ℕ) (h : 1 ≤ i ∧ i ≤ n) (p : ℤ) :
    JPower P n i p = (sysOf P n).J i p := by
  show _ = (↑(uU P n i ^ p) : NonsplitBMW P n)
  unfold JPower
  split_ifs with hp
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    simp [zpow_natCast, Units.val_pow_eq_pow_val, uU_val P n i h]
  · obtain ⟨q, hq⟩ : ∃ q : ℕ, p = -(q:ℤ) := ⟨(-p).toNat, by omega⟩
    subst hq
    simp [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, uU_inv_val P n i h]

lemma mon_list {i : ℕ} {m : NonsplitBMW P n} (h : X8L25.IsMon (uU P n) i m) (hin : i ≤ n) :
    ∃ s : Fin (i-1) → ℤ,
      m = (List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod := by
  induction h with
  | base => exact ⟨Fin.elim0, by simp⟩
  | step i m t h ih =>
    obtain ⟨s, rfl⟩ := ih (by omega)
    obtain ⟨c, rfl⟩ : ∃ c, i = c + 1 := ⟨i - 1, by have := h.pos; omega⟩
    change Fin c → ℤ at s
    change ∃ s' : Fin (c+1) → ℤ, (List.ofFn fun j : Fin c => JPower P n (j.val+1) (s j)).prod *
      ↑(uU P n (c+1) ^ t) = (List.ofFn fun j : Fin (c+1) => JPower P n (j.val+1) (s' j)).prod
    refine ⟨Fin.snoc (α := fun _ => ℤ) s t, ?_⟩
    rw [List.ofFn_succ', List.prod_concat]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
    rw [JPower_eq P n (c+1) ⟨by omega, by omega⟩]
    rfl

end X8L25C
end QAlgorithms.Papers.Independent.Gap48.P01



namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L25C

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

theorem x8_main (i : ℕ) (hi : 1 ≤ i) (hin : i < n) (p : ℤ) :
    (E P n i * JPower P n i p * E P n i ∈ Submodule.span R
      {z | ∃ s : Fin (i-1) → ℤ,
        z = (List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod * E P n i}) ∧
    (X P n i false * JPower P n i p * E P n i ∈ Submodule.span R
      {z | ∃ s : Fin (i-1) → ℤ, ∃ t : ℤ, |t| ≤ |p| ∧
        z = (List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod * JPower P n i t * E P n i}) ∧
    (E P n i * JPower P n i p * X P n i false ∈ Submodule.span R
      {z | ∃ s : Fin (i-1) → ℤ, ∃ t : ℤ, |t| ≤ |p| ∧
        z = E P n i * ((List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod * JPower P n i t)}) := by
  have hJ := JPower_eq P n i ⟨hi, hin.le⟩
  rw [hJ p]
  refine ⟨?_, ?_, ?_⟩
  · refine (Submodule.span_le.mpr ?_) ((sysOf P n).allI i hi hin p)
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨s, rfl⟩ := mon_list P n hm hin.le
    exact Submodule.subset_span ⟨s, rfl⟩
  · refine (Submodule.span_le.mpr ?_) ((sysOf P n).allII i hi hin p)
    rintro _ ⟨m, t, hm, ht, rfl⟩
    obtain ⟨s, rfl⟩ := mon_list P n hm hin.le
    exact Submodule.subset_span ⟨s, t, ht, by rw [hJ t]; rfl⟩
  · refine (Submodule.span_le.mpr ?_) ((sysOf P n).allIII i hi hin p)
    rintro _ ⟨m, t, hm, ht, rfl⟩
    obtain ⟨s, rfl⟩ := mon_list P n hm hin.le
    exact Submodule.subset_span ⟨s, t, ht, by rw [hJ t]; rfl⟩

end X8L25C

end QAlgorithms.Papers.Independent.Gap48.P01




namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L33

set_option linter.unusedSectionVars false

open X8L25C

section ip
variable {M : Type*} [Monoid M] (a : ℕ → M)

lemma ip_self (s : ℕ) : intervalProduct a s s = 1 := by simp [intervalProduct]

lemma ip_snoc {s t : ℕ} (h : s ≤ t) :
    intervalProduct a s (t+1) = intervalProduct a s t * a t := by
  unfold intervalProduct
  rw [show t + 1 - s = (t - s) + 1 by omega, List.range_succ, List.map_append, List.prod_append]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  congr 2; omega

lemma ip_cons {s t : ℕ} (h : s < t) :
    intervalProduct a s t = a s * intervalProduct a (s+1) t := by
  unfold intervalProduct
  rw [show t - s = (t - (s+1)) + 1 by omega, List.range_succ_eq_map]
  simp only [List.map_cons, List.prod_cons, List.map_map, add_zero]
  congr 2
  apply List.map_congr_left
  intro j _; simp only [Function.comp_apply]; congr 1; omega

lemma ip_one {s : ℕ} : intervalProduct a s (s+1) = a s := by
  rw [ip_snoc a le_rfl, ip_self, one_mul]

lemma ip_split {s u t : ℕ} (h1 : s ≤ u) (h2 : u ≤ t) :
    intervalProduct a s t = intervalProduct a s u * intervalProduct a u t := by
  induction t, h2 using Nat.le_induction with
  | base => rw [ip_self, mul_one]
  | succ t ht ih => rw [ip_snoc a (by omega), ip_snoc a ht, ih, mul_assoc]

lemma ip_comm (y : M) {s t : ℕ} (h : ∀ k, s ≤ k → k < t → Commute (a k) y) :
    Commute (intervalProduct a s t) y := by
  unfold intervalProduct
  apply Commute.list_prod_left
  intro z hz
  simp only [List.mem_map, List.mem_range] at hz
  obtain ⟨j, hj, rfl⟩ := hz
  exact h _ (by omega) (by omega)

end ip

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

lemma ip_mem (S : Subalgebra R (NonsplitBMW P n)) (a : ℕ → NonsplitBMW P n) {s t : ℕ}
    (h : ∀ k, s ≤ k → k < t → a k ∈ S) : intervalProduct a s t ∈ S := by
  unfold intervalProduct
  apply Subalgebra.list_prod_mem
  intro z hz
  simp only [List.mem_map, List.mem_range] at hz
  obtain ⟨j, hj, rfl⟩ := hz
  exact h _ (by omega) (by omega)

/-! level membership -/

lemma lv_X (inv : Bool) {i l : ℕ} (h1 : 1 ≤ i) (h2 : i < l) : X P n i inv ∈ level P n l :=
  Algebra.subset_adjoin (Or.inr ⟨i, h1, h2, by cases inv <;> simp⟩)

lemma lv_E {i l : ℕ} (h1 : 1 ≤ i) (h2 : i < l) : E P n i ∈ level P n l :=
  Algebra.subset_adjoin (Or.inr ⟨i, h1, h2, by simp⟩)

lemma lv_Y (inv : Bool) {l : ℕ} (h : 1 ≤ l) : Y P n inv ∈ level P n l :=
  Algebra.subset_adjoin (Or.inl ⟨h, by cases inv <;> simp⟩)

lemma lv_mono {l l' : ℕ} (h : l ≤ l') : level P n l ≤ level P n l' := by
  apply Algebra.adjoin_mono
  rintro z (⟨h1, hz⟩ | ⟨i, h1, h2, hz⟩)
  · exact Or.inl ⟨by omega, hz⟩
  · exact Or.inr ⟨i, h1, by omega, hz⟩

lemma lv_JM (inv : Bool) {i l : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ l) : JM P n inv i ∈ level P n l := by
  induction i, h1 using Nat.le_induction with
  | base => exact lv_Y P n inv (by omega)
  | succ i hi ih =>
    rw [JM_succ P n inv i hi]
    exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (lv_X P n inv hi (by omega)) (ih (by omega)))
      (lv_X P n inv hi (by omega))

lemma lv_JP {i l : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ l) (p : ℤ) : JPower P n i p ∈ level P n l := by
  unfold JPower
  split_ifs
  · exact Subalgebra.pow_mem _ (lv_JM P n false h1 h2) _
  · exact Subalgebra.pow_mem _ (lv_JM P n true h1 h2) _

lemma lv_ipX {s t l : ℕ} (hs : 1 ≤ s) (ht : t ≤ l) :
    intervalProduct (fun t => X P n t false) s t ∈ level P n l :=
  ip_mem P n _ _ (fun k h1 h2 => lv_X P n false (by omega) (by omega))

lemma lv_ipE {s t l : ℕ} (hs : 1 ≤ s) (ht : t ≤ l) :
    intervalProduct (E P n) s t ∈ level P n l :=
  ip_mem P n _ _ (fun k h1 h2 => lv_E P n (by omega) (by omega))

lemma lv_M {i l : ℕ} (h : i ≤ l + 1) (s : Fin (i-1) → ℤ) :
    (List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod ∈ level P n l := by
  apply Subalgebra.list_prod_mem
  intro z hz
  rw [List.mem_ofFn] at hz
  obtain ⟨j, rfl⟩ := hz
  exact lv_JP P n (by omega) (by have := j.isLt; omega) _

/-! alphaSpan helpers -/

lemma ac_def (i j l : ℕ) (p : ℤ) : alphaChain P n i j l p =
    JPower P n i p * intervalProduct (fun t => X P n t false) i j * intervalProduct (E P n) j (l+1) :=
  rfl

lemma as_mem {l : ℕ} {F : ℕ → ℤ → Prop} (i' j' : ℕ) (p' : ℤ) (h1 : 1 ≤ i') (h2 : i' ≤ j')
    (h3 : j' ≤ l) (hF : F i' p') {b : NonsplitBMW P n} (hb : b ∈ level P n (l-1)) :
    alphaChain P n i' j' l p' * b ∈ alphaSpan P n l F :=
  Submodule.subset_span ⟨i', j', p', h1, h2, h3, hF, b, hb, rfl⟩

lemma as_mem1 {l : ℕ} {F : ℕ → ℤ → Prop} (i' j' : ℕ) (p' : ℤ) (h1 : 1 ≤ i') (h2 : i' ≤ j')
    (h3 : j' ≤ l) (hF : F i' p') : alphaChain P n i' j' l p' ∈ alphaSpan P n l F := by
  simpa using as_mem P n i' j' p' h1 h2 h3 hF (Subalgebra.one_mem _)

lemma as_mul {l : ℕ} {F : ℕ → ℤ → Prop} {z : NonsplitBMW P n} (hz : z ∈ alphaSpan P n l F)
    {b : NonsplitBMW P n} (hb : b ∈ level P n (l-1)) : z * b ∈ alphaSpan P n l F := by
  have := X8L25.span_map (LinearMap.mulRight R b) (Q := alphaSpan P n l F) ?_ hz
  · simpa using this
  rintro _ ⟨i, j, p, h1, h2, h3, hF, b', hb', rfl⟩
  simp only [LinearMap.mulRight_apply, mul_assoc]
  exact as_mem P n i j p h1 h2 h3 hF (Subalgebra.mul_mem _ hb' hb)

lemma as_mono {l : ℕ} {F G : ℕ → ℤ → Prop} (h : ∀ i p, F i p → G i p) :
    alphaSpan P n l F ≤ alphaSpan P n l G := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, j, p, h1, h2, h3, hF, b, hb, rfl⟩
  exact as_mem P n i j p h1 h2 h3 (h i p hF) hb

end X8L33
end QAlgorithms.Papers.Independent.Gap48.P01



namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L33

set_option linter.unusedSectionVars false

open X8L25C

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

lemma eeFar (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 < j ∨ j + 1 < i) :
    E P n i * E P n j = E P n j * E P n i := by
  have := X8L25C.rel P n (NonsplitBMWRel.eeFar i j hi hj hd); simpa [E, map_mul] using this

lemma cXX {a b : ℕ} (ha : 1 ≤ a) (han : a < n) (hb : 1 ≤ b) (hbn : b < n)
    (hd : a + 1 < b ∨ b + 1 < a) : Commute (X P n a false) (X P n b false) :=
  xFar P n a b ⟨ha, han⟩ ⟨hb, hbn⟩ hd

lemma cXE {a b : ℕ} (ha : 1 ≤ a) (han : a < n) (hb : 1 ≤ b) (hbn : b < n)
    (hd : a + 1 < b ∨ b + 1 < a) : Commute (X P n a false) (E P n b) :=
  xeFar P n a b ⟨ha, han⟩ ⟨hb, hbn⟩ hd

lemma cEE {a b : ℕ} (ha : 1 ≤ a) (han : a < n) (hb : 1 ≤ b) (hbn : b < n)
    (hd : a + 1 < b ∨ b + 1 < a) : Commute (E P n a) (E P n b) :=
  eeFar P n a b ⟨ha, han⟩ ⟨hb, hbn⟩ hd

lemma cXiE {a b : ℕ} (ha : 1 ≤ a) (han : a < n) (hb : 1 ≤ b) (hbn : b < n)
    (hd : a + 1 < b ∨ b + 1 < a) : Commute (X P n a true) (E P n b) := by
  have h : X P n a true = X P n a false - skeinDelta P • (1 - E P n a) := by
    rw [← skein P n a ⟨ha, han⟩]; abel
  rw [h]
  exact (cXE P n ha han hb hbn hd).sub_left
    (((Commute.one_left _).sub_left (cEE P n ha han hb hbn hd)).smul_left _)

lemma cXiX {a b : ℕ} (ha : 1 ≤ a) (han : a < n) (hb : 1 ≤ b) (hbn : b < n)
    (hd : a + 1 < b ∨ b + 1 < a) : Commute (X P n a true) (X P n b false) := by
  have h : X P n a true = X P n a false - skeinDelta P • (1 - E P n a) := by
    rw [← skein P n a ⟨ha, han⟩]; abel
  rw [h]
  exact (cXX P n ha han hb hbn hd).sub_left
    (((Commute.one_left _).sub_left (cXE P n hb hbn ha han (by omega)).symm).smul_left _)

/-- JPower commutes with whatever JM false commutes with. -/
lemma JP_comm {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) {y : NonsplitBMW P n}
    (h : Commute (JM P n false i) y) (p : ℤ) : Commute (JPower P n i p) y := by
  rw [JPower_eq P n i ⟨hi, hin⟩]
  have h' : Commute (uU P n i : NonsplitBMW P n) y := by rw [uU_val P n i ⟨hi, hin⟩]; exact h
  exact h'.units_zpow_left p

lemma jlow (m : ℕ) (hm : 1 ≤ m) : ∀ i, m + 2 ≤ i → i ≤ n →
    Commute (JM P n false i) (X P n m false) ∧ Commute (JM P n false i) (E P n m) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro hn
    rw [JM_succ P n false (m+1) (by omega), JM_succ P n false m hm]
    set a := X P n m false
    set b := X P n (m+1) false
    set c := JM P n false m
    set e := E P n m
    set f := E P n (m+1)
    have br0 : a * (b * a) = b * (a * b) := by
      have := braid P n m ⟨hm, by omega⟩; simpa only [mul_assoc] using this
    have cb : ∀ z, c * (b * z) = b * (c * z) := by
      intro z; rw [← mul_assoc, jx_comm P n m hm (m+1) le_rfl (by omega), mul_assoc]
    have cf : ∀ z, c * (f * z) = f * (c * z) := by
      intro z; rw [← mul_assoc, je_comm P n m hm (m+1) le_rfl (by omega), mul_assoc]
    have br : ∀ z, a * (b * (a * z)) = b * (a * (b * z)) := by
      intro z; rw [← mul_assoc b, ← mul_assoc a, br0, mul_assoc, mul_assoc]
    constructor
    · show (b * (a * c * a) * b) * a = a * (b * (a * c * a) * b)
      simp only [mul_assoc]
      conv_rhs => rw [br (c * (a * b)), ← cb (a * b), ← br0]
    · show (b * (a * c * a) * b) * e = e * (b * (a * c * a) * b)
      have n1 : a * (b * e) = f * e := by
        have := nearL P n m (m+1) ⟨hm, by omega⟩ ⟨by omega, by omega⟩ (Or.inl rfl)
        simpa only [mul_assoc] using this
      have n2 : ∀ z, b * (a * (f * z)) = e * (f * z) := by
        intro z
        have := nearL P n (m+1) m ⟨by omega, by omega⟩ ⟨hm, by omega⟩ (Or.inr rfl)
        have := congrArg (· * z) this; simpa only [mul_assoc] using this
      have n3 : ∀ z, e * (b * (a * z)) = e * (f * z) := by
        intro z
        have := nearR P n (m+1) m ⟨by omega, by omega⟩ ⟨hm, by omega⟩ (Or.inr rfl)
        have := congrArg (· * z) this; simpa only [mul_assoc] using this
      have n4 : f * (a * b) = f * e := by
        have := nearR P n m (m+1) ⟨hm, by omega⟩ ⟨by omega, by omega⟩ (Or.inl rfl)
        simpa only [mul_assoc] using this
      simp only [mul_assoc]
      conv_lhs => rw [n1, cf e, n2]
      conv_rhs => rw [n3 (c * (a * b)), ← cf (a * b), n4, cf e]
  | succ i hi ih =>
    intro hn
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [JM_succ P n false i (by omega)]
    have c1 := cXX P n (a := i) (b := m) (by omega) (by omega) hm (by omega) (Or.inr (by omega))
    have c2 := cXE P n (a := i) (b := m) (by omega) (by omega) hm (by omega) (Or.inr (by omega))
    exact ⟨(c1.mul_left h1).mul_left c1, (c2.mul_left h2).mul_left c2⟩

/-- Descending inverse word X_{m+k-1}^{-1} ... X_m^{-1}. -/
def Wv (m : ℕ) : ℕ → NonsplitBMW P n
  | 0 => 1
  | k+1 => X P n (m+k) true * Wv m k

lemma lv_Wv {m L : ℕ} (hm : 1 ≤ m) : ∀ k, m + k ≤ L → Wv P n m k ∈ level P n L := by
  intro k
  induction k with
  | zero => intro _; exact Subalgebra.one_mem _
  | succ k ih =>
    intro h
    exact Subalgebra.mul_mem _ (lv_X P n true (by omega) (by omega)) (ih (by omega))

lemma Wv_comm {m : ℕ} (hm : 1 ≤ m) : ∀ k, ∀ t, m + k + 1 ≤ t → t < n →
    Commute (Wv P n m k) (X P n t false) ∧ Commute (Wv P n m k) (E P n t) := by
  intro k
  induction k with
  | zero => intro t _ _; exact ⟨Commute.one_left _, Commute.one_left _⟩
  | succ k ih =>
    intro t ht htn
    obtain ⟨h1, h2⟩ := ih t (by omega) htn
    exact ⟨(cXiX P n (by omega) (by omega) (by omega) htn (Or.inl (by omega))).mul_left h1,
      (cXiE P n (by omega) (by omega) (by omega) htn (Or.inl (by omega))).mul_left h2⟩

lemma ex_shift {a : ℕ} (ha : 1 ≤ a) (han : a + 1 < n) :
    E P n a * X P n (a+1) false = E P n a * E P n (a+1) * X P n a true := by
  rw [← nearR P n (a+1) a ⟨by omega, han⟩ ⟨ha, by omega⟩ (Or.inr rfl), mul_assoc _ (X P n a false),
    x_xi P n a ⟨ha, by omega⟩, mul_one]

lemma shift {m : ℕ} (hm : 1 ≤ m) : ∀ k, m + 1 + k ≤ n →
    E P n m * intervalProduct (fun t => X P n t false) (m+1) (m+1+k) =
      intervalProduct (E P n) m (m+1+k) * Wv P n m k := by
  intro k
  induction k with
  | zero => intro _; simp [ip_self, ip_one, Wv]
  | succ k ih =>
    intro hk
    have hc := (Wv_comm P n hm k (m+1+k) (by omega) (by omega)).1
    calc E P n m * intervalProduct (fun t => X P n t false) (m+1) (m+1+(k+1))
        = E P n m * intervalProduct (fun t => X P n t false) (m+1) (m+1+k) * X P n (m+1+k) false := by
          rw [show m + 1 + (k+1) = (m+1+k) + 1 by omega, ip_snoc _ (by omega), mul_assoc]
      _ = intervalProduct (E P n) m (m+1+k) * (Wv P n m k * X P n (m+1+k) false) := by
          rw [ih (by omega), mul_assoc]
      _ = intervalProduct (E P n) m (m+k) * (E P n (m+k) * X P n (m+k+1) false) * Wv P n m k := by
          rw [hc.eq, show m + 1 + k = (m+k) + 1 by omega, ip_snoc _ (by omega : m ≤ m + k)]
          simp only [mul_assoc]
      _ = intervalProduct (E P n) m (m+1+(k+1)) * Wv P n m (k+1) := by
          rw [ex_shift P n (by omega) (by omega), show m + 1 + (k+1) = (m+k+1) + 1 by omega,
            ip_snoc _ (by omega : m ≤ m + k + 1), ip_snoc _ (by omega : m ≤ m + k)]
          simp only [Wv, mul_assoc]

/-- e_m X_{m+1}..X_{j-1} e_j..e_l = e_m..e_l * W with W ∈ level (l-1). -/
lemma shiftE {m j l : ℕ} (hm : 1 ≤ m) (hmj : m + 1 ≤ j) (hjl : j ≤ l) (hl : l < n) :
    E P n m * intervalProduct (fun t => X P n t false) (m+1) j * intervalProduct (E P n) j (l+1) =
      intervalProduct (E P n) m (l+1) * Wv P n m (j - (m+1)) ∧
    Wv P n m (j - (m+1)) ∈ level P n (l-1) := by
  refine ⟨?_, lv_Wv P n hm _ (by omega)⟩
  have h := shift P n hm (j - (m+1)) (by omega)
  rw [show m + 1 + (j - (m+1)) = j by omega] at h
  have hc : Commute (Wv P n m (j - (m+1))) (intervalProduct (E P n) j (l+1)) := by
    apply Commute.symm
    apply ip_comm
    intro t ht1 ht2
    have := (Wv_comm P n hm (j - (m+1)) t (by omega) (by omega)).2
    exact this.symm
  calc E P n m * intervalProduct (fun t => X P n t false) (m+1) j * intervalProduct (E P n) j (l+1)
      = intervalProduct (E P n) m j * Wv P n m (j - (m+1)) * intervalProduct (E P n) j (l+1) := by
        rw [h]
    _ = intervalProduct (E P n) m j * intervalProduct (E P n) j (l+1) * Wv P n m (j - (m+1)) := by
        rw [mul_assoc, hc.eq, ← mul_assoc]
    _ = _ := by rw [← ip_split _ (by omega) (by omega)]

end X8L33
end QAlgorithms.Papers.Independent.Gap48.P01



namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L33

set_option linter.unusedSectionVars false

open X8L25C

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

def G1 (i m : ℕ) (p : ℤ) : ℕ → ℤ → Prop := fun ip pp => min i m ≤ ip ∧ |pp| ≤ |p| ∧ 0 ≤ pp * p

lemma JP_zero (i : ℕ) : JPower P n i 0 = 1 := by simp [JPower]

lemma ac00 (m l : ℕ) : alphaChain P n m m l 0 = intervalProduct (E P n) m (l+1) := by
  rw [ac_def, JP_zero, ip_self]; simp

lemma cJE_hi {i t : ℕ} (hi : 1 ≤ i) (h : i + 1 ≤ t) (htn : t < n) (p : ℤ) :
    Commute (JPower P n i p) (E P n t) :=
  JP_comm P n hi (by omega) (je_comm P n i hi t h htn) p

lemma cJX_hi {i t : ℕ} (hi : 1 ≤ i) (h : i + 1 ≤ t) (htn : t < n) (p : ℤ) :
    Commute (JPower P n i p) (X P n t false) :=
  JP_comm P n hi (by omega) (jx_comm P n i hi t h htn) p

lemma cJE_lo {i t : ℕ} (ht : 1 ≤ t) (h : t + 2 ≤ i) (hin : i ≤ n) (p : ℤ) :
    Commute (JPower P n i p) (E P n t) :=
  JP_comm P n (by omega) hin (jlow P n t ht i h hin).2 p

lemma cJX_lo {i t : ℕ} (ht : 1 ≤ t) (h : t + 2 ≤ i) (hin : i ≤ n) (p : ℤ) :
    Commute (JPower P n i p) (X P n t false) :=
  JP_comm P n (by omega) hin (jlow P n t ht i h hin).1 p

lemma c_ipE {y : NonsplitBMW P n} {s u : ℕ} (h : ∀ t, s ≤ t → t < u → Commute y (E P n t)) :
    Commute y (intervalProduct (E P n) s u) :=
  (ip_comm _ y (fun t h1 h2 => (h t h1 h2).symm)).symm

lemma c_ipX {y : NonsplitBMW P n} {s u : ℕ} (h : ∀ t, s ≤ t → t < u → Commute y (X P n t false)) :
    Commute y (intervalProduct (fun t => X P n t false) s u) :=
  (ip_comm _ y (fun t h1 h2 => (h t h1 h2).symm)).symm

lemma cM {i : ℕ} (s : Fin (i-1) → ℤ) {y : NonsplitBMW P n}
    (h : ∀ j, 1 ≤ j → j + 1 ≤ i → Commute (JM P n false j) y) (hin : i ≤ n + 1) :
    Commute (List.ofFn fun j : Fin (i-1) => JPower P n (j.val+1) (s j)).prod y := by
  apply Commute.list_prod_left
  intro z hz
  rw [List.mem_ofFn] at hz
  obtain ⟨j, rfl⟩ := hz
  exact JP_comm P n (by omega) (by have := j.isLt; omega) (h _ (by omega) (by have := j.isLt; omega)) _

lemma m9R' {a : ℕ} (ha : 1 ≤ a) (han : a < n) (t : ℤ) :
    E P n a * JPower P n (a+1) t = E P n a * JPower P n a (-t) := by
  rw [JPower_eq P n (a+1) ⟨by omega, by omega⟩, JPower_eq P n a ⟨ha, by omega⟩]
  exact (sysOf P n).m9Rz ha han t

lemma m9L' {a : ℕ} (ha : 1 ≤ a) (han : a < n) (t : ℤ) :
    JPower P n (a+1) t * E P n a = JPower P n a (-t) * E P n a := by
  rw [JPower_eq P n (a+1) ⟨by omega, by omega⟩, JPower_eq P n a ⟨ha, by omega⟩]
  exact (sysOf P n).m9Lz ha han t

lemma JP_add {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (s t : ℤ) :
    JPower P n i (s + t) = JPower P n i s * JPower P n i t := by
  rw [JPower_eq P n i ⟨hi, hin⟩, JPower_eq P n i ⟨hi, hin⟩, JPower_eq P n i ⟨hi, hin⟩]
  exact (sysOf P n).J_add i s t

/-! The action of e_m. -/

lemma e2 {m l : ℕ} (hm : 1 ≤ m) (hml : m ≤ l) (hl : l < n) (p : ℤ) :
    E P n m * alphaChain P n m m l p ∈ alphaSpan P n l (G1 m m p) := by
  have h := (x8_main P n m hm (by omega) p).1
  have e1 : E P n m * alphaChain P n m m l p =
      E P n m * JPower P n m p * E P n m * intervalProduct (E P n) (m+1) (l+1) := by
    rw [ac_def, ip_self, mul_one, ip_cons _ (by omega : m < l + 1)]; simp only [mul_assoc]
  rw [e1]
  refine X8L25.span_map (LinearMap.mulRight R (intervalProduct (E P n) (m+1) (l+1))) ?_ h
  rintro _ ⟨s, rfl⟩
  simp only [LinearMap.mulRight_apply]
  have hc := cM P n s (y := intervalProduct (E P n) m (l+1))
    (fun j hj hji => (ip_comm _ _ (fun t ht1 ht2 =>
      (je_comm P n j hj t (by omega) (by omega)).symm)).symm) (by omega)
  rw [mul_assoc, ← ip_cons _ (by omega : m < l + 1), hc.eq, ← ac00]
  exact as_mem P n m m 0 hm le_rfl hml ⟨by simp, by simp, by simp⟩ (lv_M P n (by omega) s)

lemma e1 {m j l : ℕ} (hm : 1 ≤ m) (hmj : m < j) (hjl : j ≤ l) (hl : l < n) (p : ℤ) :
    E P n m * alphaChain P n m j l p ∈ alphaSpan P n l (G1 m m p) := by
  have h := (x8_main P n m hm (by omega) p).2.2
  have e1 : E P n m * alphaChain P n m j l p =
      E P n m * JPower P n m p * X P n m false *
        (intervalProduct (fun t => X P n t false) (m+1) j * intervalProduct (E P n) j (l+1)) := by
    rw [ac_def, ip_cons _ hmj]; simp only [mul_assoc]
  rw [e1]
  refine X8L25.span_map (LinearMap.mulRight R _) ?_ h
  rintro _ ⟨s, t, ht, rfl⟩
  simp only [LinearMap.mulRight_apply]
  obtain ⟨hsh, hW⟩ := shiftE P n hm hmj hjl hl
  set Mo := (List.ofFn fun j : Fin (m-1) => JPower P n (j.val+1) (s j)).prod
  have hMo : Mo ∈ level P n (l-1) := lv_M P n (by omega) s
  set K := Mo * JPower P n m t with hK
  have hcX : Commute K (intervalProduct (fun t => X P n t false) (m+1) j) :=
    c_ipX P n (fun u hu1 hu2 => (cM P n s (fun j' hj' hj'm =>
      jx_comm P n j' hj' u (by omega) (by omega)) (by omega)).mul_left
      (cJX_hi P n hm (by omega) (by omega) t))
  have hcE : Commute K (intervalProduct (E P n) j (l+1)) :=
    c_ipE P n (fun u hu1 hu2 => (cM P n s (fun j' hj' hj'm =>
      je_comm P n j' hj' u (by omega) (by omega)) (by omega)).mul_left
      (cJE_hi P n hm (by omega) (by omega) t))
  have : E P n m * K *
      (intervalProduct (fun t => X P n t false) (m+1) j * intervalProduct (E P n) j (l+1)) =
      alphaChain P n m m l 0 * (Wv P n m (j - (m+1)) * K) := by
    rw [ac00]
    simp only [mul_assoc]
    rw [hcX.left_comm, hcE.eq, ← mul_assoc, ← mul_assoc, hsh, mul_assoc]
  rw [this]
  exact as_mem P n m m 0 hm le_rfl (by omega) ⟨by simp, by simp, by simp⟩
    (Subalgebra.mul_mem _ hW (Subalgebra.mul_mem _ hMo (lv_JP P n hm (by omega) t)))

lemma e3 {m j l : ℕ} (hm : 1 ≤ m) (hmj : m + 1 ≤ j) (hjl : j ≤ l) (hl : l < n) (p : ℤ) :
    E P n m * alphaChain P n (m+1) j l p ∈ alphaSpan P n l (G1 (m+1) m p) := by
  obtain ⟨hsh, hW⟩ := shiftE P n hm hmj hjl hl
  have hcX : Commute (JPower P n m (-p)) (intervalProduct (fun t => X P n t false) (m+1) j) :=
    c_ipX P n (fun u hu1 hu2 => cJX_hi P n hm (by omega) (by omega) _)
  have hcE : Commute (JPower P n m (-p)) (intervalProduct (E P n) j (l+1)) :=
    c_ipE P n (fun u hu1 hu2 => cJE_hi P n hm (by omega) (by omega) _)
  have : E P n m * alphaChain P n (m+1) j l p =
      alphaChain P n m m l 0 * (Wv P n m (j - (m+1)) * JPower P n m (-p)) := by
    rw [ac_def, ← mul_assoc, ← mul_assoc, m9R' P n hm (by omega), mul_assoc (E P n m), hcX.eq,
      ← mul_assoc, mul_assoc _ (JPower P n m (-p)), hcE.eq, ← mul_assoc, hsh, ac00]
    simp only [mul_assoc]
  rw [this]
  exact as_mem P n m m 0 hm le_rfl (by omega) ⟨by simp, by simp, by simp⟩
    (Subalgebra.mul_mem _ hW (lv_JP P n hm (by omega) _))

lemma e4a {i j l m : ℕ} (hm : 1 ≤ m) (hmi : m + 2 ≤ i) (hij : i ≤ j) (hjl : j ≤ l) (hl : l < n)
    (p : ℤ) : E P n m * alphaChain P n i j l p ∈ alphaSpan P n l (G1 i m p) := by
  have h1 : Commute (E P n m) (JPower P n i p) := (cJE_lo P n hm hmi (by omega) p).symm
  have h2 : Commute (E P n m) (intervalProduct (fun t => X P n t false) i j) :=
    c_ipX P n (fun u hu1 hu2 => (cXE P n (by omega) (by omega) hm (by omega) (Or.inr (by omega))).symm)
  have h3 : Commute (E P n m) (intervalProduct (E P n) j (l+1)) :=
    c_ipE P n (fun u hu1 hu2 => cEE P n hm (by omega) (by omega) (by omega) (Or.inl (by omega)))
  rw [ac_def, ((h1.mul_right h2).mul_right h3).eq]
  exact as_mem P n i j p (by omega) hij hjl ⟨by omega, le_rfl, mul_self_nonneg p⟩
    (lv_E P n hm (by omega))

lemma e4b {i j l m : ℕ} (hi : 1 ≤ i) (him : i + 1 ≤ m) (hij : i ≤ j) (hml : m ≤ l) (hjl : j ≤ l)
    (hl : l < n) (p : ℤ) : E P n m * alphaChain P n i j l p ∈ alphaSpan P n l (G1 i m p) := by
  have hF : G1 i m p m 0 := ⟨by omega, by simp, by simp⟩
  set J := JPower P n i p
  set e := E P n m
  have hJe : Commute J e := cJE_hi P n hi him (by omega) p
  have hJEe : Commute J (intervalProduct (E P n) m (l+1)) :=
    c_ipE P n (fun u hu1 hu2 => cJE_hi P n hi (by omega) (by omega) p)
  rcases Nat.lt_trichotomy m j with hmj | rfl | hmj
  · -- m < j
    obtain ⟨hsh, hW⟩ := shiftE P n (by omega : 1 ≤ m) (by omega : m + 1 ≤ j) hjl hl
    set A := intervalProduct (fun t => X P n t false) i (m-1)
    set B := intervalProduct (fun t => X P n t false) (m+1) j
    set C := intervalProduct (E P n) j (l+1)
    set f := E P n (m-1)
    have hA : intervalProduct (fun t => X P n t false) i j = A * (X P n (m-1) false * (X P n m false * B)) := by
      rw [ip_split _ (by omega : i ≤ m - 1) (by omega : m - 1 ≤ j), ip_cons _ (by omega : m - 1 < j),
        show m - 1 + 1 = m by omega, ip_cons _ hmj]
    have hAe' : Commute A e := (ip_comm _ e (fun u hu1 hu2 =>
      cXE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))))
    have hAEe : Commute A (intervalProduct (E P n) m (l+1)) :=
      ip_comm _ _ (fun u hu1 hu2 => c_ipE P n (fun t ht1 ht2 =>
        cXE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))))
    have nr : ∀ z, e * (X P n (m-1) false * (X P n m false * z)) = e * (f * z) := by
      intro z
      have := nearR P n (m-1) m ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inl (by omega))
      have := congrArg (· * z) this
      simpa only [mul_assoc, show m - 1 + 1 = m by omega] using this
    have hfB : Commute f B := c_ipX P n (fun u hu1 hu2 =>
      (cXE P n (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))).symm)
    have hfC : Commute f C := c_ipE P n (fun u hu1 hu2 =>
      cEE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)))
    have : e * alphaChain P n i j l p =
        alphaChain P n m m l 0 * (J * (A * (Wv P n m (j - (m+1)) * f))) := by
      rw [ac_def, hA, ac00]
      simp only [mul_assoc]
      rw [hJe.symm.left_comm, hAe'.symm.left_comm, nr, hfB.left_comm, hfC.eq,
        show e * (B * (C * f)) = (e * B * C) * f by simp only [mul_assoc], hsh,
        mul_assoc, hAEe.left_comm, hJEe.left_comm]
    rw [this]
    exact as_mem P n m m 0 (by omega) le_rfl hml hF
      (Subalgebra.mul_mem _ (lv_JP P n hi (by omega) p) (Subalgebra.mul_mem _
        (lv_ipX P n hi (by omega)) (Subalgebra.mul_mem _ hW (lv_E P n (by omega) (by omega)))))
  · -- m = j
    set A := intervalProduct (fun t => X P n t false) i (m-1)
    set Ef := intervalProduct (E P n) (m+1) (l+1)
    have hA : intervalProduct (fun t => X P n t false) i m = A * X P n (m-1) false := by
      rw [show m = (m-1) + 1 by omega, ip_snoc _ (by omega)]; simp [A]
    have hEm : intervalProduct (E P n) m (l+1) = e * Ef := ip_cons _ (by omega)
    have hAe' : Commute A e := (ip_comm _ e (fun u hu1 hu2 =>
      cXE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))))
    have hAEe : Commute A (intervalProduct (E P n) m (l+1)) :=
      ip_comm _ _ (fun u hu1 hu2 => c_ipE P n (fun t ht1 ht2 =>
        cXE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))))
    have h0 : E P n m * X P n (m-1) false * E P n m = (↑P.lam⁻¹ : R) • E P n m := by
      have := (sysOf P n).exe (a := m-1) (by omega) (by omega)
      rw [show m - 1 + 1 = m by omega] at this
      exact this
    have exe : ∀ z, e * (X P n (m-1) false * (e * z)) = (↑P.lam⁻¹ : R) • (e * z) := by
      intro z
      have := congrArg (· * z) h0
      simpa only [mul_assoc, smul_mul_assoc] using this
    have : e * alphaChain P n i m l p =
        (↑P.lam⁻¹ : R) • (alphaChain P n m m l 0 * (J * A)) := by
      rw [ac_def, hA, ac00]
      nth_rewrite 1 [hEm]
      simp only [mul_assoc]
      rw [hJe.symm.left_comm, hAe'.symm.left_comm, exe, mul_smul_comm, mul_smul_comm, ← hEm,
        ← mul_assoc J A, (hJEe.mul_left hAEe).eq]
    rw [this]
    exact Submodule.smul_mem _ _ (as_mem P n m m 0 (by omega) le_rfl hml hF
      (Subalgebra.mul_mem _ (lv_JP P n hi (by omega) p) (lv_ipX P n hi (by omega))))
  · -- m > j
    set B0 := intervalProduct (fun t => X P n t false) i j
    set D := intervalProduct (E P n) j (m-1)
    set f := E P n (m-1)
    set Ef := intervalProduct (E P n) (m+1) (l+1)
    have hC : intervalProduct (E P n) j (l+1) = D * (f * (e * Ef)) := by
      rw [ip_split _ (by omega : j ≤ m - 1) (by omega : m - 1 ≤ l + 1), ip_cons _ (by omega : m - 1 < l + 1),
        show m - 1 + 1 = m by omega, ip_cons _ (by omega : m < l + 1)]
    have hEm : intervalProduct (E P n) m (l+1) = e * Ef := ip_cons _ (by omega)
    have hB0e : Commute B0 e := ip_comm _ e (fun u hu1 hu2 =>
      cXE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)))
    have hDe : Commute D e := ip_comm _ e (fun u hu1 hu2 =>
      cEE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)))
    have hB0E : Commute B0 (intervalProduct (E P n) m (l+1)) :=
      ip_comm _ _ (fun u hu1 hu2 => c_ipE P n (fun t ht1 ht2 =>
        cXE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))))
    have hDE : Commute D (intervalProduct (E P n) m (l+1)) :=
      ip_comm _ _ (fun u hu1 hu2 => c_ipE P n (fun t ht1 ht2 =>
        cEE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))))
    have tr : ∀ z, e * (f * (e * z)) = e * z := by
      intro z
      have := tripleE P n m (m-1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
      have := congrArg (· * z) this; simpa only [mul_assoc] using this
    have : e * alphaChain P n i j l p = alphaChain P n m m l 0 * (J * (B0 * D)) := by
      rw [ac_def, hC, ac00]
      simp only [mul_assoc]
      rw [hJe.symm.left_comm, hB0e.symm.left_comm, hDe.symm.left_comm, tr, ← hEm,
        ← mul_assoc B0 D, ← mul_assoc J, (hJEe.mul_left (hB0E.mul_left hDE)).eq]
    rw [this]
    exact as_mem P n m m 0 (by omega) le_rfl hml hF
      (Subalgebra.mul_mem _ (lv_JP P n hi (by omega) p) (Subalgebra.mul_mem _
        (lv_ipX P n hi (by omega)) (lv_ipE P n (by omega) (by omega))))

end X8L33
end QAlgorithms.Papers.Independent.Gap48.P01



namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L33

set_option linter.unusedSectionVars false

open X8L25C

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

lemma pN (j r : ℕ) : JM P n false j ^ r = JPower P n j r := by simp [JPower]

lemma pI (j r : ℕ) : JM P n true j ^ r = JPower P n j (-(r:ℤ)) := by
  unfold JPower
  split_ifs with h
  · obtain rfl : r = 0 := by omega
    simp
  · simp

lemma cJJ' {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ n) (s t : ℤ) :
    Commute (JPower P n a s) (JPower P n b t) :=
  JP_comm P n ha (by omega) (JP_comm P n (by omega) hb (jj_comm P n a ha b hab hb).symm t).symm s

/-- Case (A): X_m alpha_{m+1,j,l}^p. -/
lemma xA {m j l : ℕ} (hm : 1 ≤ m) (hmj : m + 1 ≤ j) (hjl : j ≤ l) (hl : l < n) (p : ℤ) :
    X P n m false * alphaChain P n (m+1) j l p ∈ alphaSpan P n l (G1 (m+1) m p) := by
  obtain ⟨hsh, hW⟩ := shiftE P n hm hmj hjl hl
  set B := intervalProduct (fun t => X P n t false) (m+1) j
  set C := intervalProduct (E P n) j (l+1)
  set W := Wv P n m (j - (m+1))
  have hmn : m < n := by omega
  have hcB : ∀ a : ℤ, Commute (JPower P n m a) B := fun a =>
    c_ipX P n (fun u hu1 hu2 => cJX_hi P n hm (by omega) (by omega) a)
  have hcC : ∀ a : ℤ, Commute (JPower P n m a) C := fun a =>
    c_ipE P n (fun u hu1 hu2 => cJE_hi P n hm (by omega) (by omega) a)
  have tA1 : ∀ a : ℤ, JPower P n m a * X P n m false * (B * C) = alphaChain P n m j l a := by
    intro a; rw [ac_def, ip_cons _ (by omega : m < j)]; simp only [mul_assoc]; all_goals rfl
  have tA2 : ∀ a b : ℤ, JPower P n m a * JPower P n (m+1) b * (B * C) =
      alphaChain P n (m+1) j l b * JPower P n m a := by
    intro a b
    rw [ac_def, mul_assoc, ((cJJ' P n hm (by omega) (by omega) a b).mul_right
      ((hcB a).mul_right (hcC a))).eq]
    simp only [mul_assoc]; all_goals rfl
  have tA3 : ∀ a b : ℤ, JPower P n m a * E P n m * JPower P n (m+1) b * (B * C) =
      alphaChain P n m m l a * (W * JPower P n m (-b)) := by
    intro a b
    rw [mul_assoc (JPower P n m a), m9R' P n hm hmn, ac_def, ip_self, mul_one]
    have : E P n m * JPower P n m (-b) * (B * C) = E P n m * B * C * JPower P n m (-b) := by
      rw [mul_assoc, ((hcB (-b)).mul_right (hcC (-b))).eq]; simp only [mul_assoc]
    rw [mul_assoc, this, hsh]; simp only [mul_assoc]
  have hx1 := x_xi P n m ⟨hm, hmn⟩
  have hx2 := xi_x P n m ⟨hm, hmn⟩
  have hsk := skein P n m ⟨hm, hmn⟩
  have hxe : X P n m false * E P n m = E P n m * X P n m false := by
    rw [xe P n m ⟨hm, hmn⟩, ex P n m ⟨hm, hmn⟩]
  have hv := JM_succ P n false m hm
  have hvi := JM_succ P n true m hm
  rcases le_or_gt 0 p with hp | hp
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    have g := X8B24.g27 (skeinDelta P) _ _ _ _ _ _ _ hx1 hx2 hsk hxe hv hvi q
    have e0 : X P n m false * alphaChain P n (m+1) j l q =
        (X P n m false * JM P n false (m+1) ^ q) * (B * C) := by
      rw [ac_def, pN]; simp only [mul_assoc]; all_goals rfl
    rw [e0, g, sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc, Finset.sum_mul, Finset.sum_mul]
    refine sub_mem (add_mem ?_ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t ht => ?_)))
      (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t ht => ?_))
    · rw [pN, tA1]
      exact as_mem1 P n m j q hm (by omega) (by omega) ⟨by omega, le_rfl, mul_self_nonneg _⟩
    · rw [Finset.mem_range] at ht
      rw [pN, pN, tA2]
      exact as_mem P n (m+1) j _ (by omega) hmj hjl
        ⟨by omega, by simp only [abs_neg, Nat.abs_cast]; omega, by positivity⟩
        (lv_JP P n hm (by omega) _)
    · rw [Finset.mem_range] at ht
      rw [pN, pN, tA3]
      exact as_mem P n m m _ hm le_rfl (by omega)
        ⟨by omega, by simp only [abs_neg, Nat.abs_cast]; omega, by positivity⟩
        (Subalgebra.mul_mem _ hW (lv_JP P n hm (by omega) _))
  · obtain ⟨q, hq⟩ : ∃ q : ℕ, p = -(q:ℤ) := ⟨(-p).toNat, by omega⟩
    subst hq
    have g := X8B24.g28 (skeinDelta P) _ _ _ _ _ _ _ hx1 hx2 hsk hxe hv hvi q
    have e0 : X P n m false * alphaChain P n (m+1) j l (-(q:ℤ)) =
        (X P n m false * JM P n true (m+1) ^ q) * (B * C) := by
      rw [ac_def, pI]; simp only [mul_assoc]; all_goals rfl
    rw [e0, g, add_mul, sub_mul, smul_mul_assoc, smul_mul_assoc, Finset.sum_mul, Finset.sum_mul]
    refine add_mem (sub_mem ?_ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t ht => ?_)))
      (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t ht => ?_))
    · rw [pI, tA1]
      exact as_mem1 P n m j _ hm (by omega) (by omega) ⟨by omega, le_rfl, mul_self_nonneg _⟩
    · rw [Finset.mem_range] at ht
      rw [pI, pI, tA2]
      refine as_mem P n (m+1) j _ (by omega) hmj hjl
        ⟨by omega, by simp only [abs_neg, Nat.abs_cast]; omega, ?_⟩
        (lv_JP P n hm (by omega) _)
      have : (0:ℤ) ≤ ((q - (t+1) : ℕ) : ℤ) := by positivity
      nlinarith
    · rw [Finset.mem_range] at ht
      rw [pI, pI, tA3]
      refine as_mem P n m m _ hm le_rfl (by omega)
        ⟨by omega, by simp only [abs_neg, Nat.abs_cast]; omega, ?_⟩
        (Subalgebra.mul_mem _ hW (lv_JP P n hm (by omega) _))
      push_cast; nlinarith

end X8L33
end QAlgorithms.Papers.Independent.Gap48.P01



namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L33

set_option linter.unusedSectionVars false

open X8L25C

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

def GX (i m : ℕ) (p : ℤ) : ℕ → ℤ → Prop := fun ip pp =>
  (min i m ≤ ip ∧ |pp| ≤ |p| ∧ 0 ≤ pp * p) ∨ (ip = m ∧ m = i ∧ |pp| ≤ |p|)

def G3 (m : ℕ) (p : ℤ) : ℕ → ℤ → Prop := fun ip pp => ip = m ∧ |pp| ≤ |p|

lemma sign_trans {pp r q : ℤ} (h1 : |pp| ≤ |r|) (h2 : 0 ≤ pp * r) (h3 : 0 ≤ r * q) :
    0 ≤ pp * q := by
  rcases eq_or_ne r 0 with rfl | hr
  · have : pp = 0 := abs_nonpos_iff.mp (by simpa using h1)
    simp [this]
  · have hrr : 0 < r * r := mul_self_pos.mpr hr
    have h4 : 0 ≤ pp * q * (r * r) := by
      have := mul_nonneg h2 h3
      linarith [show (pp * r) * (r * q) = pp * q * (r * r) by ring]
    by_contra hc
    have : pp * q * (r * r) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hc) hrr
    linarith

/-- Case (B): X_m alpha_{m,m,l}^p. -/
lemma xB {m l : ℕ} (hm : 1 ≤ m) (hml : m ≤ l) (hl : l < n) (p : ℤ) :
    X P n m false * alphaChain P n m m l p ∈ alphaSpan P n l (G3 m p) := by
  have h := (x8_main P n m hm (by omega) p).2.1
  have e1 : X P n m false * alphaChain P n m m l p =
      X P n m false * JPower P n m p * E P n m * intervalProduct (E P n) (m+1) (l+1) := by
    rw [ac_def, ip_self, mul_one, ip_cons _ (by omega : m < l + 1)]; simp only [mul_assoc]
  rw [e1]
  refine X8L25.span_map (LinearMap.mulRight R (intervalProduct (E P n) (m+1) (l+1))) ?_ h
  rintro _ ⟨s, t, ht, rfl⟩
  simp only [LinearMap.mulRight_apply]
  have hc : Commute (List.ofFn fun j : Fin (m-1) => JPower P n (j.val+1) (s j)).prod
      (JPower P n m t * intervalProduct (E P n) m (l+1)) :=
    cM P n s (fun j hj hjm => (JP_comm P n (i := m) (by omega) (by omega)
      (jj_comm P n j hj m (by omega) (by omega)).symm t).symm.mul_right
      (c_ipE P n (fun u hu1 hu2 => je_comm P n j hj u (by omega) (by omega)))) (by omega)
  rw [mul_assoc, ← ip_cons _ (by omega : m < l + 1), mul_assoc, hc.eq]
  have : JPower P n m t * intervalProduct (E P n) m (l+1) = alphaChain P n m m l t := by
    rw [ac_def, ip_self, mul_one]
  rw [this]
  exact as_mem P n m m t hm le_rfl hml ⟨rfl, ht⟩ (lv_M P n (by omega) s)

lemma xx_quad {m : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    X P n m false * X P n m false =
      1 + skeinDelta P • X P n m false - (skeinDelta P * (P.lam : R)) • E P n m := by
  have h : X P n m false = X P n m true + skeinDelta P • (1 - E P n m) := by
    rw [← skein P n m ⟨hm, hmn⟩]; abel
  conv_lhs => rw [show X P n m false * X P n m false =
    X P n m false * (X P n m true + skeinDelta P • (1 - E P n m)) by rw [← h]]
  rw [mul_add, x_xi P n m ⟨hm, hmn⟩, mul_smul_comm, mul_sub, mul_one, xe P n m ⟨hm, hmn⟩,
    smul_sub, smul_smul]; abel

/-- Case (C): X_m alpha_{m,j,l}^p with m < j. -/
lemma xC {m j l : ℕ} (hm : 1 ≤ m) (hmj : m < j) (hjl : j ≤ l) (hl : l < n) (p : ℤ) :
    X P n m false * alphaChain P n m j l p ∈ alphaSpan P n l (GX m m p) := by
  obtain ⟨hsh, hW⟩ := shiftE P n hm hmj hjl hl
  set B := intervalProduct (fun t => X P n t false) (m+1) j
  set C := intervalProduct (E P n) j (l+1)
  set W := Wv P n m (j - (m+1))
  have hmn : m < n := by omega
  have hcB : ∀ a : ℤ, Commute (JPower P n m a) B := fun a =>
    c_ipX P n (fun u hu1 hu2 => cJX_hi P n hm (by omega) (by omega) a)
  have hcC : ∀ a : ℤ, Commute (JPower P n m a) C := fun a =>
    c_ipE P n (fun u hu1 hu2 => cJE_hi P n hm (by omega) (by omega) a)
  have e0 : X P n m false * alphaChain P n m j l p =
      (X P n m false * JPower P n m p * X P n m false) * (B * C) := by
    rw [ac_def, ip_cons _ hmj]; simp only [mul_assoc]; all_goals rfl
  -- term shapes
  have t1 : ∀ b : ℤ, JPower P n (m+1) b * (B * C) = alphaChain P n (m+1) j l b := by
    intro b; rw [ac_def]; simp only [mul_assoc]; all_goals rfl
  have t2 : ∀ a b : ℤ, X P n m false * JPower P n m a * JPower P n (m+1) b * (B * C) =
      X P n m false * alphaChain P n (m+1) j l b * JPower P n m a := by
    intro a b
    rw [← t1 b]
    simp only [mul_assoc]
    rw [((cJJ' P n hm (by omega) (by omega) a b).mul_right ((hcB a).mul_right (hcC a))).eq]
    simp only [mul_assoc]
  have t3 : ∀ a b : ℤ, X P n m false * JPower P n m a * E P n m * JPower P n (m+1) b * (B * C) =
      X P n m false * alphaChain P n m m l a * (W * JPower P n m (-b)) := by
    intro a b
    rw [mul_assoc _ (E P n m), m9R' P n hm hmn, ac_def, ip_self, mul_one]
    have : E P n m * JPower P n m (-b) * (B * C) = E P n m * B * C * JPower P n m (-b) := by
      rw [mul_assoc, ((hcB (-b)).mul_right (hcC (-b))).eq]; simp only [mul_assoc]
    rw [mul_assoc, this, hsh]; simp only [mul_assoc]
  have mapA : ∀ r : ℤ, |r| ≤ |p| → 0 ≤ r * p → ∀ ip pp, G1 (m+1) m r ip pp → GX m m p ip pp := by
    intro r hr hrp ip pp ⟨h1, h2, h3⟩
    exact Or.inl ⟨by omega, h2.trans hr, sign_trans h2 h3 hrp⟩
  have mapB : ∀ t : ℤ, |t| ≤ |p| → ∀ ip pp, G3 m t ip pp → GX m m p ip pp := by
    intro t ht ip pp ⟨h1, h2⟩
    exact Or.inr ⟨h1, rfl, h2.trans ht⟩
  have hx1 := x_xi P n m ⟨hm, hmn⟩
  have hx2 := xi_x P n m ⟨hm, hmn⟩
  have hsk := skein P n m ⟨hm, hmn⟩
  have hxe : X P n m false * E P n m = E P n m * X P n m false := by
    rw [xe P n m ⟨hm, hmn⟩, ex P n m ⟨hm, hmn⟩]
  have hv := JM_succ P n false m hm
  have hvi := JM_succ P n true m hm
  rcases le_or_gt 0 p with hp | hp
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    rcases q with _ | q
    · -- p = 0
      rw [e0, Nat.cast_zero, JP_zero, mul_one, xx_quad P n hm hmn, sub_mul, add_mul, one_mul,
        smul_mul_assoc, smul_mul_assoc]
      refine sub_mem (add_mem ?_ (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ ?_)
      · have := t1 0; rw [JP_zero, one_mul] at this; rw [this]
        exact as_mem1 P n (m+1) j 0 (by omega) hmj hjl (Or.inl ⟨by omega, by simp, by simp⟩)
      · have : X P n m false * (B * C) = alphaChain P n m j l 0 := by
          rw [ac_def, JP_zero, one_mul, ip_cons _ hmj]; simp only [mul_assoc]; all_goals rfl
        rw [this]
        exact as_mem1 P n m j 0 hm hmj.le hjl (Or.inl ⟨by omega, by simp, by simp⟩)
      · rw [← mul_assoc, hsh, ← ac00]
        exact as_mem P n m m 0 hm le_rfl (by omega) (Or.inl ⟨by omega, by simp, by simp⟩) hW
    · have g := X8B24.g30 (skeinDelta P) _ _ _ _ _ _ _ hx1 hx2 hsk hxe hv hvi q
      rw [e0, ← pN, g, add_mul, sub_mul, smul_mul_assoc, smul_mul_assoc, Finset.sum_mul,
        Finset.sum_mul]
      refine add_mem (sub_mem ?_ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t ht => ?_)))
        (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t ht => ?_))
      · rw [pN, t1]
        exact as_mem1 P n (m+1) j _ (by omega) hmj hjl
          (Or.inl ⟨by omega, le_rfl, mul_self_nonneg _⟩)
      · rw [Finset.mem_range] at ht
        rw [pN, pN, t2]
        refine as_mono P n (mapA _ ?_ ?_) (as_mul P n (xA P n hm hmj hjl hl _)
          (lv_JP P n hm (by omega) _))
        · simp only [Nat.abs_cast]; omega
        · positivity
      · rw [Finset.mem_range] at ht
        rw [pN, pN, t3]
        refine as_mono P n (mapB _ ?_) (as_mul P n (xB P n hm (by omega) hl _)
          (Subalgebra.mul_mem _ hW (lv_JP P n hm (by omega) _)))
        simp only [Nat.abs_cast]; omega
  · obtain ⟨q, hq⟩ : ∃ q : ℕ, p = -(q:ℤ) := ⟨(-p).toNat, by omega⟩
    subst hq
    have g := X8B24.g32 (skeinDelta P) _ _ _ _ _ _ _ hx1 hx2 hsk hxe hv hvi q
    rw [e0, ← pI, g, sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc, Finset.sum_mul,
      Finset.sum_mul]
    refine sub_mem (add_mem ?_ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t ht => ?_)))
      (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t ht => ?_))
    · rw [pI, t1]
      exact as_mem1 P n (m+1) j _ (by omega) hmj hjl
        (Or.inl ⟨by omega, le_rfl, mul_self_nonneg _⟩)
    · rw [Finset.mem_range] at ht
      rw [pI, pI, t2]
      refine as_mono P n (mapA _ ?_ ?_) (as_mul P n (xA P n hm hmj hjl hl _)
        (lv_JP P n hm (by omega) _))
      · simp only [abs_neg, Nat.abs_cast]; omega
      · push_cast; nlinarith
    · rw [Finset.mem_range] at ht
      rw [pI, pI, t3]
      refine as_mono P n (mapB _ ?_) (as_mul P n (xB P n hm (by omega) hl _)
        (Subalgebra.mul_mem _ hW (lv_JP P n hm (by omega) _)))
      simp only [abs_neg, Nat.abs_cast]; omega

end X8L33
end QAlgorithms.Papers.Independent.Gap48.P01



namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L33

set_option linter.unusedSectionVars false

open X8L25C

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

lemma xD1 {i j l m : ℕ} (hm : 1 ≤ m) (hmi : m + 2 ≤ i) (hij : i ≤ j) (hjl : j ≤ l) (hl : l < n)
    (p : ℤ) : X P n m false * alphaChain P n i j l p ∈ alphaSpan P n l (G1 i m p) := by
  have h1 : Commute (X P n m false) (JPower P n i p) := (cJX_lo P n hm hmi (by omega) p).symm
  have h2 : Commute (X P n m false) (intervalProduct (fun t => X P n t false) i j) :=
    c_ipX P n (fun u hu1 hu2 => cXX P n hm (by omega) (by omega) (by omega) (Or.inl (by omega)))
  have h3 : Commute (X P n m false) (intervalProduct (E P n) j (l+1)) :=
    c_ipE P n (fun u hu1 hu2 => cXE P n hm (by omega) (by omega) (by omega) (Or.inl (by omega)))
  rw [ac_def, ((h1.mul_right h2).mul_right h3).eq]
  exact as_mem P n i j p (by omega) hij hjl ⟨by omega, le_rfl, mul_self_nonneg p⟩
    (lv_X P n false hm (by omega))

lemma xfe {m : ℕ} (hm : 2 ≤ m) (hmn : m < n) :
    X P n m false * (E P n (m-1) * E P n m) =
      X P n (m-1) false * E P n m + skeinDelta P • (E P n (m-1) * E P n m) -
        skeinDelta P • E P n m := by
  have hnl : X P n m false * X P n (m-1) false * E P n m = E P n (m-1) * E P n m :=
    nearL P n m (m-1) ⟨by omega, hmn⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
  have h0 : E P n m * X P n (m-1) false * E P n m = (↑P.lam⁻¹ : R) • E P n m := by
    have := (sysOf P n).exe (a := m-1) (by omega) (by omega)
    rw [show m - 1 + 1 = m by omega] at this
    exact this
  rw [← hnl, ← mul_assoc, ← mul_assoc, xx_quad P n (by omega) hmn]
  simp only [add_mul, sub_mul, one_mul, smul_mul_assoc]
  rw [hnl, mul_assoc (E P n m), ← mul_assoc (E P n m) _ (E P n m), h0, smul_smul, mul_assoc,
    Units.mul_inv, mul_one]

lemma xD2 {i j l m : ℕ} (hi : 1 ≤ i) (him : i + 1 ≤ m) (hij : i ≤ j) (hml : m ≤ l) (hjl : j ≤ l)
    (hl : l < n) (p : ℤ) : X P n m false * alphaChain P n i j l p ∈ alphaSpan P n l (G1 i m p) := by
  set J := JPower P n i p
  set b := X P n m false
  have hJb : Commute J b := cJX_hi P n hi him (by omega) p
  rcases Nat.lt_trichotomy m j with hmj | rfl | hmj
  · set A := intervalProduct (fun t => X P n t false) i (m-1)
    set a := X P n (m-1) false
    set B := intervalProduct (fun t => X P n t false) (m+1) j
    set C := intervalProduct (E P n) j (l+1)
    have hA : intervalProduct (fun t => X P n t false) i j = A * (a * (b * B)) := by
      rw [ip_split _ (by omega : i ≤ m - 1) (by omega : m - 1 ≤ j), ip_cons _ (by omega : m - 1 < j),
        show m - 1 + 1 = m by omega, ip_cons _ hmj]
    have hAb : Commute A b := ip_comm _ b (fun u hu1 hu2 =>
      cXX P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)))
    have br : ∀ z, b * (a * (b * z)) = a * (b * (a * z)) := by
      intro z
      have := braid P n (m-1) ⟨by omega, by omega⟩
      rw [show m - 1 + 1 = m by omega] at this
      have := congrArg (· * z) this
      simpa only [mul_assoc] using this.symm
    have haB : Commute a B := c_ipX P n (fun u hu1 hu2 =>
      cXX P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)))
    have haC : Commute a C := c_ipE P n (fun u hu1 hu2 =>
      cXE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)))
    have : b * alphaChain P n i j l p = alphaChain P n i j l p * a := by
      rw [ac_def, hA]
      simp only [mul_assoc]
      rw [hJb.symm.left_comm, hAb.symm.left_comm, br, haB.left_comm, haC.eq]
    rw [this]
    exact as_mem P n i j p hi hij hjl ⟨by omega, le_rfl, mul_self_nonneg p⟩
      (lv_X P n false (by omega) (by omega))
  · set A := intervalProduct (fun t => X P n t false) i (m-1)
    set Ef := intervalProduct (E P n) (m+1) (l+1)
    have hA : intervalProduct (fun t => X P n t false) i m = A * X P n (m-1) false := by
      rw [show m = (m-1) + 1 by omega, ip_snoc _ (by omega)]; simp [A]
    have hEm : intervalProduct (E P n) m (l+1) = E P n m * Ef := ip_cons _ (by omega)
    have hAb : Commute A b := ip_comm _ b (fun u hu1 hu2 =>
      cXX P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)))
    have nl : ∀ z, b * (X P n (m-1) false * (E P n m * z)) = E P n (m-1) * (E P n m * z) := by
      intro z
      have := nearL P n m (m-1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
      have := congrArg (· * z) this; simpa only [mul_assoc] using this
    have : b * alphaChain P n i m l p = alphaChain P n i (m-1) l p := by
      rw [ac_def, hA, hEm, ac_def, ip_cons _ (by omega : m - 1 < l + 1), show m - 1 + 1 = m by omega,
        hEm]
      simp only [mul_assoc]
      rw [hJb.symm.left_comm, hAb.symm.left_comm, nl]
    rw [this]
    exact as_mem1 P n i (m-1) p hi (by omega) (by omega) ⟨by omega, le_rfl, mul_self_nonneg p⟩
  · set B0 := intervalProduct (fun t => X P n t false) i j
    set D := intervalProduct (E P n) j (m-1)
    set f := E P n (m-1)
    set e := E P n m
    set Ef := intervalProduct (E P n) (m+1) (l+1)
    have hC : intervalProduct (E P n) j (l+1) = D * (f * (e * Ef)) := by
      rw [ip_split _ (by omega : j ≤ m - 1) (by omega : m - 1 ≤ l + 1), ip_cons _ (by omega : m - 1 < l + 1),
        show m - 1 + 1 = m by omega, ip_cons _ (by omega : m < l + 1)]
    have hEm : intervalProduct (E P n) m (l+1) = e * Ef := ip_cons _ (by omega)
    have hB0b : Commute B0 b := ip_comm _ b (fun u hu1 hu2 =>
      cXX P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)))
    have hDb : Commute D b := ip_comm _ b (fun u hu1 hu2 =>
      (cXE P n (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))).symm)
    have hJE : Commute J (intervalProduct (E P n) m (l+1)) :=
      c_ipE P n (fun u hu1 hu2 => cJE_hi P n hi (by omega) (by omega) p)
    have hB0E : Commute B0 (intervalProduct (E P n) m (l+1)) :=
      ip_comm _ _ (fun u hu1 hu2 => c_ipE P n (fun t ht1 ht2 =>
        cXE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))))
    have hDE : Commute D (intervalProduct (E P n) m (l+1)) :=
      ip_comm _ _ (fun u hu1 hu2 => c_ipE P n (fun t ht1 ht2 =>
        cEE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))))
    have hq := xfe P n (m := m) (by omega) (by omega)
    have key : b * alphaChain P n i j l p =
        J * (B0 * (D * (X P n (m-1) false * (e * Ef)))) + skeinDelta P • alphaChain P n i j l p -
          skeinDelta P • (alphaChain P n m m l 0 * (J * (B0 * D))) := by
      have h3 : J * (B0 * (D * (e * Ef))) = alphaChain P n m m l 0 * (J * (B0 * D)) := by
        rw [ac00, ← hEm, ← mul_assoc B0 D, ← mul_assoc J, (hJE.mul_left (hB0E.mul_left hDE)).eq]
      rw [← h3, ac_def, hC]
      simp only [mul_assoc]
      rw [hJb.symm.left_comm, hB0b.symm.left_comm, hDb.symm.left_comm,
        show b * (f * (e * Ef)) = (b * (f * e)) * Ef by simp only [mul_assoc], hq]
      simp only [add_mul, sub_mul, smul_mul_assoc, mul_add, mul_sub, mul_smul_comm, mul_assoc]
      all_goals rfl
    rw [key]
    refine sub_mem (add_mem ?_ (Submodule.smul_mem _ _ (as_mem1 P n i j p hi hij hjl
      ⟨by omega, le_rfl, mul_self_nonneg p⟩))) (Submodule.smul_mem _ _
      (as_mem P n m m 0 (by omega) le_rfl hml ⟨by omega, by simp, by simp⟩
        (Subalgebra.mul_mem _ (lv_JP P n hi (by omega) p) (Subalgebra.mul_mem _
          (lv_ipX P n hi (by omega)) (lv_ipE P n (by omega) (by omega))))))
    rcases Nat.lt_or_ge j (m-1) with hj2 | hj2
    · -- j ≤ m - 2
      set D' := intervalProduct (E P n) j (m-2)
      have hD : D = D' * E P n (m-2) := by
        show intervalProduct (E P n) j (m-1) = intervalProduct (E P n) j (m-2) * E P n (m-2)
        rw [show m - 1 = (m-2) + 1 by omega, ip_snoc _ (by omega)]
      have hsh := ex_shift P n (a := m-2) (by omega) (by omega)
      rw [show m - 2 + 1 = m - 1 by omega] at hsh
      have hXe : Commute (X P n (m-2) true) e :=
        cXiE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
      have hXEf : Commute (X P n (m-2) true) Ef := c_ipE P n (fun u hu1 hu2 =>
        cXiE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)))
      have : J * (B0 * (D * (X P n (m-1) false * (e * Ef)))) =
          alphaChain P n i j l p * X P n (m-2) true := by
        rw [ac_def, hC, hD]
        simp only [mul_assoc]
        rw [← mul_assoc (E P n (m-2)), hsh]
        simp only [mul_assoc]
        rw [hXe.left_comm, hXEf.eq]
        all_goals rfl
      rw [this]
      exact as_mem P n i j p hi hij hjl ⟨by omega, le_rfl, mul_self_nonneg p⟩
        (lv_X P n true (by omega) (by omega))
    · obtain rfl : j = m - 1 := by omega
      have : J * (B0 * (D * (X P n (m-1) false * (e * Ef)))) = alphaChain P n i m l p := by
        have hD1 : D = 1 := ip_self (E P n) (m-1)
        have hB0X : B0 * X P n (m-1) false = intervalProduct (fun t => X P n t false) i m := by
          have := ip_snoc (fun t => X P n t false) hij
          rw [show m - 1 + 1 = m by omega] at this
          exact this.symm
        rw [ac_def, hD1, one_mul, ← mul_assoc B0, hB0X, hEm]
        simp only [mul_assoc]
        all_goals rfl
      rw [this]
      exact as_mem1 P n i m p hi (by omega) hml ⟨by omega, le_rfl, mul_self_nonneg p⟩

end X8L33
end QAlgorithms.Papers.Independent.Gap48.P01



namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L33

open X8L25C

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

theorem x8_main33 (l i j m : ℕ) (hl : l < n)
    (hi : 1 ≤ i) (hij : i ≤ j) (hjl : j ≤ l) (hm : 1 ≤ m) (hml : m ≤ l)
    (p : ℤ) (g : ℕ → NonsplitBMW P n) (hg : g = (fun t => X P n t false) ∨ g = E P n) :
    g m * alphaChain P n i j l p ∈ alphaSpan P n l
      (fun ip pp => min i m ≤ ip ∧ |pp| ≤ |p| ∧
        (pp*p < 0 → ip = m ∧ m = i ∧ g = (fun t => X P n t false))) := by
  have hG1 : ∀ i' : ℕ, i' = i → alphaSpan P n l (G1 i' m p) ≤ alphaSpan P n l
      (fun ip pp => min i m ≤ ip ∧ |pp| ≤ |p| ∧
        (pp*p < 0 → ip = m ∧ m = i ∧ g = (fun t => X P n t false))) := by
    rintro i' rfl
    exact as_mono P n (fun ip pp ⟨h1, h2, h3⟩ => ⟨h1, h2, fun h => absurd h (not_lt.mpr h3)⟩)
  rcases hg with rfl | rfl
  · have hGX : alphaSpan P n l (GX i m p) ≤ alphaSpan P n l
        (fun ip pp => min i m ≤ ip ∧ |pp| ≤ |p| ∧
          (pp*p < 0 → ip = m ∧ m = i ∧ (fun t => X P n t false) = (fun t => X P n t false))) := by
      refine as_mono P n (fun ip pp h => ?_)
      rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact ⟨h1, h2, fun h => absurd h (not_lt.mpr h3)⟩
      · exact ⟨by omega, h3, fun _ => ⟨h1, h2, rfl⟩⟩
    show X P n m false * alphaChain P n i j l p ∈ _
    rcases (by omega : m + 2 ≤ i ∨ i = m + 1 ∨ i = m ∨ i + 1 ≤ m) with h | h | h | h
    · exact hG1 i rfl (xD1 P n hm h hij hjl hl p)
    · subst h; exact hG1 (m+1) rfl (xA P n hm hij hjl hl p)
    · subst h
      rcases eq_or_lt_of_le hij with rfl | hlt
      · refine as_mono P n (fun ip pp h => ?_) (xB P n hm hml hl p)
        obtain ⟨h1, h2⟩ := h
        exact ⟨by omega, h2, fun _ => ⟨h1, rfl, rfl⟩⟩
      · exact hGX (xC P n hm hlt hjl hl p)
    · exact hG1 i rfl (xD2 P n hi h hij hml hjl hl p)
  · show E P n m * alphaChain P n i j l p ∈ _
    rcases (by omega : m + 2 ≤ i ∨ i = m + 1 ∨ i = m ∨ i + 1 ≤ m) with h | h | h | h
    · exact hG1 i rfl (e4a P n hm h hij hjl hl p)
    · subst h; exact hG1 (m+1) rfl (e3 P n hm hij hjl hl p)
    · subst h
      rcases eq_or_lt_of_le hij with rfl | hlt
      · exact hG1 _ rfl (e2 P n hm hml hl p)
      · exact hG1 i rfl (e1 P n hm hlt hjl hl p)
    · exact hG1 i rfl (e4b P n hi h hij hml hjl hl p)

end X8L33

end QAlgorithms.Papers.Independent.Gap48.P01


noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L35

set_option linter.unusedSectionVars false

open X8L25C X8L33

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

/-! triple-e shift relations -/

lemma triX {a : ℕ} (ha : 1 ≤ a) (han : a + 2 < n) :
    E P n a * E P n (a+1) * E P n (a+2) * X P n a false =
      X P n (a+2) false * (E P n a * E P n (a+1) * E P n (a+2)) := by
  have c1 : E P n (a+2) * X P n a false = X P n a false * E P n (a+2) :=
    (cXE P n (a := a) (b := a+2) ha (by omega) (by omega) han (Or.inl (by omega))).eq.symm
  have n1 : E P n (a+1) * X P n a false = E P n (a+1) * E P n a * X P n (a+1) true := by
    have h := nearR P n a (a+1) ⟨ha, by omega⟩ ⟨by omega, by omega⟩ (Or.inl rfl)
    rw [← h, mul_assoc _ (X P n (a+1) false), x_xi P n (a+1) ⟨by omega, by omega⟩, mul_one]
  have t1 : E P n a * E P n (a+1) * E P n a = E P n a :=
    tripleE P n a (a+1) ⟨ha, by omega⟩ ⟨by omega, by omega⟩ (Or.inl rfl)
  have c2 : X P n (a+2) false * E P n a = E P n a * X P n (a+2) false :=
    (cXE P n (a := a+2) (b := a) (by omega) han ha (by omega) (Or.inr (by omega))).eq
  have n2 : X P n (a+2) false * E P n (a+1) * E P n (a+2) = X P n (a+1) true * E P n (a+2) := by
    have h := nearL P n (a+1) (a+2) ⟨by omega, by omega⟩ ⟨by omega, han⟩ (Or.inl rfl)
    have t2 := tripleE P n (a+2) (a+1) ⟨by omega, han⟩ ⟨by omega, by omega⟩ (Or.inr rfl)
    have h2 : X P n (a+1) false * (X P n (a+2) false * E P n (a+1) * E P n (a+2)) = E P n (a+2) := by
      calc X P n (a+1) false * (X P n (a+2) false * E P n (a+1) * E P n (a+2))
          = (X P n (a+1) false * X P n (a+2) false * E P n (a+1)) * E P n (a+2) := by
            simp only [mul_assoc]
        _ = E P n (a+2) := by rw [h, t2]
    have := congrArg (X P n (a+1) true * ·) h2
    simp only [← mul_assoc, xi_x P n (a+1) ⟨by omega, by omega⟩, one_mul] at this
    rw [this]
  calc E P n a * E P n (a+1) * E P n (a+2) * X P n a false
      = E P n a * (E P n (a+1) * X P n a false) * E P n (a+2) := by
        rw [mul_assoc _ (E P n (a+2)), c1]; simp only [mul_assoc]
    _ = E P n a * X P n (a+1) true * E P n (a+2) := by
        rw [n1, ← mul_assoc, ← mul_assoc, t1]
    _ = E P n a * (X P n (a+2) false * E P n (a+1) * E P n (a+2)) := by
        rw [n2, mul_assoc]
    _ = X P n (a+2) false * (E P n a * E P n (a+1) * E P n (a+2)) := by
        simp only [← mul_assoc, c2]

lemma triE {a : ℕ} (ha : 1 ≤ a) (han : a + 2 < n) :
    E P n a * E P n (a+1) * E P n (a+2) * E P n a =
      E P n (a+2) * (E P n a * E P n (a+1) * E P n (a+2)) := by
  have c : E P n (a+2) * E P n a = E P n a * E P n (a+2) :=
    (cEE P n (a := a+2) (b := a) (by omega) han ha (by omega) (Or.inr (by omega))).eq
  have t1 : E P n a * E P n (a+1) * E P n a = E P n a :=
    tripleE P n a (a+1) ⟨ha, by omega⟩ ⟨by omega, by omega⟩ (Or.inl rfl)
  have t2 : E P n (a+2) * E P n (a+1) * E P n (a+2) = E P n (a+2) :=
    tripleE P n (a+2) (a+1) ⟨by omega, han⟩ ⟨by omega, by omega⟩ (Or.inr rfl)
  have L : E P n a * E P n (a+1) * E P n (a+2) * E P n a = E P n a * E P n (a+2) := by
    calc E P n a * E P n (a+1) * E P n (a+2) * E P n a
        = E P n a * E P n (a+1) * (E P n (a+2) * E P n a) := by simp only [mul_assoc]
      _ = (E P n a * E P n (a+1) * E P n a) * E P n (a+2) := by rw [c]; simp only [mul_assoc]
      _ = _ := by rw [t1]
  have R : E P n (a+2) * (E P n a * E P n (a+1) * E P n (a+2)) = E P n a * E P n (a+2) := by
    calc E P n (a+2) * (E P n a * E P n (a+1) * E P n (a+2))
        = (E P n (a+2) * E P n a) * E P n (a+1) * E P n (a+2) := by simp only [mul_assoc]
      _ = E P n a * (E P n (a+2) * E P n (a+1) * E P n (a+2)) := by rw [c]; simp only [mul_assoc]
      _ = _ := by rw [t2]
  rw [L, R]

lemma triJ {a : ℕ} (ha : 1 ≤ a) (han : a + 2 < n) (t : ℤ) :
    E P n a * E P n (a+1) * E P n (a+2) * JPower P n a t =
      JPower P n (a+2) t * (E P n a * E P n (a+1) * E P n (a+2)) := by
  have c1 := (cJE_hi P n (i := a) (t := a+1) ha le_rfl (by omega) t).eq
  have c2 := (cJE_hi P n (i := a) (t := a+2) ha (by omega) han t).eq
  have m1 : E P n a * JPower P n a t = E P n a * JPower P n (a+1) (-t) := by
    rw [m9R' P n ha (by omega) (-t), neg_neg]
  have m2 : JPower P n (a+1) (-t) * E P n (a+1) = JPower P n (a+2) t * E P n (a+1) :=
    (m9L' P n (a := a+1) (by omega) (by omega) t).symm
  have c3 := (cJE_lo P n (i := a+2) (t := a) ha le_rfl (by omega) t).eq
  calc E P n a * E P n (a+1) * E P n (a+2) * JPower P n a t
      = E P n a * JPower P n a t * E P n (a+1) * E P n (a+2) := by
        simp only [mul_assoc]; rw [← c2, ← mul_assoc (E P n (a+1)), ← c1]; simp only [mul_assoc]
    _ = E P n a * (JPower P n (a+1) (-t) * E P n (a+1)) * E P n (a+2) := by
        rw [m1]; simp only [mul_assoc]
    _ = JPower P n (a+2) t * (E P n a * E P n (a+1) * E P n (a+2)) := by
        rw [m2, ← mul_assoc, ← c3]; simp only [mul_assoc]

lemma ipE_tri {j a l : ℕ} (hja : j ≤ a) (hal : a + 2 ≤ l) :
    intervalProduct (E P n) j (l+1) = intervalProduct (E P n) j a *
      (E P n a * E P n (a+1) * E P n (a+2)) * intervalProduct (E P n) (a+3) (l+1) := by
  rw [ip_split _ hja (by omega : a ≤ l+1), ip_cons (E P n) (show a < l+1 by omega),
    ip_cons (E P n) (show a+1 < l+1 by omega), ip_cons (E P n) (show a+1+1 < l+1 by omega)]
  simp only [mul_assoc, show a + 1 + 1 + 1 = a + 3 by omega, show a + 1 + 1 = a + 2 by omega]

lemma I1gen {j a l : ℕ} (hja : j ≤ a) (hal : a + 2 ≤ l) (x y : NonsplitBMW P n)
    (hfar : Commute x (intervalProduct (E P n) (a+3) (l+1)))
    (hlow : Commute y (intervalProduct (E P n) j a))
    (htri : E P n a * E P n (a+1) * E P n (a+2) * x = y * (E P n a * E P n (a+1) * E P n (a+2))) :
    intervalProduct (E P n) j (l+1) * x = y * intervalProduct (E P n) j (l+1) := by
  rw [ipE_tri P n hja hal]
  calc intervalProduct (E P n) j a * (E P n a * E P n (a+1) * E P n (a+2)) *
        intervalProduct (E P n) (a+3) (l+1) * x
      = intervalProduct (E P n) j a * ((E P n a * E P n (a+1) * E P n (a+2)) * x) *
        intervalProduct (E P n) (a+3) (l+1) := by
        rw [mul_assoc _ _ x, ← hfar.eq]; simp only [mul_assoc]
    _ = _ := by
        rw [htri, ← mul_assoc, ← hlow.eq]; simp only [mul_assoc]

lemma shX {j a l : ℕ} (hj : 1 ≤ j) (hja : j ≤ a) (hal : a + 2 ≤ l) (hl : l < n) :
    intervalProduct (E P n) j (l+1) * X P n a false =
      X P n (a+2) false * intervalProduct (E P n) j (l+1) :=
  I1gen P n hja hal _ _
    (c_ipE.{u_1} P n (fun t h1 h2 => cXE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))))
    (c_ipE P n (fun t h1 h2 => cXE P n (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))))
    (triX P n (by omega) (by omega))

lemma shE {j a l : ℕ} (hj : 1 ≤ j) (hja : j ≤ a) (hal : a + 2 ≤ l) (hl : l < n) :
    intervalProduct (E P n) j (l+1) * E P n a = E P n (a+2) * intervalProduct (E P n) j (l+1) :=
  I1gen P n hja hal _ _
    (c_ipE P n (fun t h1 h2 => cEE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))))
    (c_ipE P n (fun t h1 h2 => cEE P n (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))))
    (triE P n (by omega) (by omega))

lemma shJ {j a l : ℕ} (hj : 1 ≤ j) (hja : j ≤ a) (hal : a + 2 ≤ l) (hl : l < n) (t : ℤ) :
    intervalProduct (E P n) j (l+1) * JPower P n a t =
      JPower P n (a+2) t * intervalProduct (E P n) j (l+1) :=
  I1gen P n hja hal _ _
    (c_ipE P n (fun s h1 h2 => cJE_hi P n (by omega) (by omega) (by omega) t))
    (c_ipE P n (fun s h1 h2 => cJE_lo P n (by omega) (by omega) (by omega) t))
    (triJ P n (by omega) (by omega) t)

lemma ip_shift {M : Type*} [Monoid M] (a : ℕ → M) (c : M) {s u : ℕ} (hsu : s ≤ u)
    (h : ∀ t, s ≤ t → t < u → c * a t = a (t+2) * c) :
    c * intervalProduct a s u = intervalProduct a (s+2) (u+2) * c := by
  induction u, hsu using Nat.le_induction with
  | base => simp [ip_self]
  | succ u hu ih =>
    rw [ip_snoc _ hu, show u + 1 + 2 = (u+2) + 1 by omega, ip_snoc _ (by omega : s + 2 ≤ u + 2),
      ← mul_assoc, ih (fun t h1 h2 => h t h1 (by omega)), mul_assoc, h u hu (by omega), ← mul_assoc]

/-- e_j..e_l * alpha^r_{g,h,l-2} = alpha^r_{g+2,h+2,l} * e_j..e_l -/
lemma shA {j g h l : ℕ} (hj : 1 ≤ j) (hjg : j ≤ g) (hgh : g ≤ h) (hhl : h + 2 ≤ l) (hl : l < n)
    (r : ℤ) :
    intervalProduct (E P n) j (l+1) * alphaChain P n g h (l-2) r =
      alphaChain P n (g+2) (h+2) l r * intervalProduct (E P n) j (l+1) := by
  rw [ac_def, ac_def, show l - 2 + 1 = l - 1 by omega]
  have e1 := ip_shift (fun t => X P n t false) (intervalProduct (E P n) j (l+1)) hgh
    (fun t h1 h2 => shX P n hj (by omega) (by omega) hl)
  have e2 := ip_shift (E P n) (intervalProduct (E P n) j (l+1)) (by omega : h ≤ l - 1)
    (fun t h1 h2 => shE P n hj (by omega) (by omega) hl)
  rw [show l - 1 + 2 = l + 1 by omega] at e2
  simp only [← mul_assoc]
  rw [shJ P n hj hjg (by omega) hl r, mul_assoc _ _ (intervalProduct (fun t => X P n t false) g h), e1,
    ← mul_assoc, mul_assoc _ _ (intervalProduct (E P n) h (l-1)), e2, ← mul_assoc]

/-- absorbing e_{l-1} e_l -/
lemma absorb {j h l : ℕ} (hj : 1 ≤ j) (hjl : j + 1 ≤ l) (hhl : h ≤ l) (hl : l < n) :
    intervalProduct (E P n) h (l+1) * intervalProduct (E P n) j (l+1) =
      intervalProduct (E P n) h (l+1) * intervalProduct (E P n) j (l-1) := by
  have s1 : intervalProduct (E P n) j (l+1) = intervalProduct (E P n) j (l-1) * E P n (l-1) * E P n l := by
    rw [ip_snoc _ (by omega), show l = (l-1) + 1 by omega, ip_snoc _ (by omega)]
    simp only [show l - 1 + 1 = l by omega]
  have s2 : intervalProduct (E P n) h (l+1) = intervalProduct (E P n) h l * E P n l := ip_snoc _ hhl
  have c : Commute (E P n l) (intervalProduct (E P n) j (l-1)) :=
    c_ipE P n (fun t h1 h2 => cEE P n (by omega) hl (by omega) (by omega) (Or.inr (by omega)))
  have t : E P n l * E P n (l-1) * E P n l = E P n l :=
    tripleE P n l (l-1) ⟨by omega, hl⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
  rw [s1, s2]
  calc intervalProduct (E P n) h l * E P n l * (intervalProduct (E P n) j (l-1) * E P n (l-1) * E P n l)
      = intervalProduct (E P n) h l * (E P n l * intervalProduct (E P n) j (l-1)) * E P n (l-1) * E P n l := by
        simp only [mul_assoc]
    _ = intervalProduct (E P n) h l * intervalProduct (E P n) j (l-1) * (E P n l * E P n (l-1) * E P n l) := by
        rw [c.eq]; simp only [mul_assoc]
    _ = _ := by rw [t, mul_assoc, ← c.eq, ← mul_assoc]

/-- Case g ≥ j of Lemma 3.5. -/
lemma caseGJ {i j g h l : ℕ} (hl : l < n) (hi : 1 ≤ i) (hij : i ≤ j) (hjg : j ≤ g) (hgh : g ≤ h)
    (hhl : h + 2 ≤ l) (p r : ℤ) :
    alphaChain P n i j l p * alphaChain P n g h (l-2) r =
      alphaChain P n (g+2) (h+2) l r * alphaChain P n i j (l-2) p := by
  have hA := shA P n (by omega : 1 ≤ j) hjg hgh hhl hl r
  have hab := absorb P n (j := j) (h := h+2) (l := l) (by omega) (by omega) hhl hl
  have cJ : Commute (JPower P n i p) (alphaChain P n (g+2) (h+2) l r) := by
    rw [ac_def]
    refine ((cJJ' P n hi (by omega) (by omega) p r).mul_right ?_).mul_right ?_
    · exact c_ipX P n (fun t h1 h2 => cJX_hi P n hi (by omega) (by omega) p)
    · exact c_ipE P n (fun t h1 h2 => cJE_hi P n hi (by omega) (by omega) p)
  have cX : Commute (intervalProduct (fun t => X P n t false) i j) (alphaChain P n (g+2) (h+2) l r) := by
    apply Commute.symm
    apply c_ipX P n
    intro t ht1 ht2
    rw [ac_def]
    refine ((cJX_lo P n (by omega) (by omega) (by omega) r).mul_left ?_).mul_left ?_
    · exact (c_ipX P n (fun s hs1 hs2 => cXX P n (a := t) (b := s) (by omega) (by omega) (by omega)
        (by omega) (Or.inl (by omega)))).symm
    · exact (c_ipE P n (fun s hs1 hs2 => cXE P n (a := t) (b := s) (by omega) (by omega) (by omega)
        (by omega) (Or.inl (by omega)))).symm
  have hA' : alphaChain P n (g+2) (h+2) l r * intervalProduct (E P n) j (l+1) =
      alphaChain P n (g+2) (h+2) l r * intervalProduct (E P n) j (l-1) := by
    rw [ac_def, mul_assoc, hab, ← mul_assoc]
  set Al := alphaChain P n (g+2) (h+2) l r
  calc alphaChain P n i j l p * alphaChain P n g h (l-2) r
      = JPower P n i p * intervalProduct (fun t => X P n t false) i j *
          (intervalProduct (E P n) j (l+1) * alphaChain P n g h (l-2) r) := by
        rw [ac_def P n i j l]; simp only [mul_assoc]
    _ = JPower P n i p * intervalProduct (fun t => X P n t false) i j *
          (Al * intervalProduct (E P n) j (l-1)) := by rw [hA, hA']
    _ = JPower P n i p * (intervalProduct (fun t => X P n t false) i j * Al) *
          intervalProduct (E P n) j (l-1) := by simp only [mul_assoc]
    _ = (JPower P n i p * Al) * intervalProduct (fun t => X P n t false) i j *
          intervalProduct (E P n) j (l-1) := by rw [cX.eq]; simp only [mul_assoc]
    _ = _ := by
        rw [cJ.eq, ac_def P n i j (l-2), show l - 2 + 1 = l - 1 by omega]; simp only [mul_assoc]

end X8L35

end QAlgorithms.Papers.Independent.Gap48.P01

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L35

set_option linter.unusedSectionVars false

open X8L25C X8L33

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

local notation "δ" => skeinDelta P
local notation "XX" => fun t => X P n t false

lemma xie {m : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    X P n m true * E P n m = (↑P.lam⁻¹ : R) • E P n m := by
  have h := congrArg (X P n m true * ·) (xe P n m ⟨hm, hmn⟩)
  simp only [← mul_assoc, xi_x P n m ⟨hm, hmn⟩, one_mul, mul_smul_comm] at h
  calc X P n m true * E P n m = (↑P.lam⁻¹ : R) • ((P.lam : R) • (X P n m true * E P n m)) := by
        rw [smul_smul, Units.inv_mul, one_smul]
    _ = _ := by rw [← h]

lemma eXr {m : ℕ} (hm : 1 ≤ m) (hmn : m + 1 < n) :
    E P n m * X P n (m+1) false = E P n m * E P n (m+1) * X P n m true := by
  have h := nearR P n (m+1) m ⟨by omega, hmn⟩ ⟨hm, by omega⟩ (Or.inr rfl)
  rw [← h, mul_assoc _ (X P n m false), x_xi P n m ⟨hm, by omega⟩, mul_one]

lemma eXl {m : ℕ} (hm : 1 ≤ m) (hmn : m + 1 < n) :
    E P n (m+1) * X P n m false = E P n (m+1) * E P n m * X P n (m+1) true := by
  have h := nearR P n m (m+1) ⟨hm, by omega⟩ ⟨by omega, hmn⟩ (Or.inl rfl)
  rw [← h, mul_assoc _ (X P n (m+1) false), x_xi P n (m+1) ⟨by omega, hmn⟩, mul_one]

lemma K0 {m : ℕ} (hm : 1 ≤ m) (hmn : m + 1 < n) :
    E P n m * X P n (m+1) false * E P n m = (↑P.lam⁻¹ : R) • E P n m := by
  rw [eXr P n hm hmn, mul_assoc, xie P n hm (by omega), mul_smul_comm,
    tripleE P n m (m+1) ⟨hm, by omega⟩ ⟨by omega, hmn⟩ (Or.inl rfl)]

lemma K1 {m : ℕ} (hm : 1 ≤ m) (hmn : m + 1 < n) :
    X P n m false * (E P n (m+1) * E P n m) =
      X P n (m+1) false * E P n m + δ • (E P n (m+1) * E P n m) - δ • E P n m := by
  have nl := nearL P n m (m+1) ⟨hm, by omega⟩ ⟨by omega, hmn⟩ (Or.inl rfl)
  have q := xx_quad P n hm (by omega)
  have k0 := K0 P n hm hmn
  rw [← nl]
  calc X P n m false * (X P n m false * X P n (m+1) false * E P n m)
      = (X P n m false * X P n m false) * X P n (m+1) false * E P n m := by simp only [mul_assoc]
    _ = X P n (m+1) false * E P n m + δ • (X P n m false * X P n (m+1) false * E P n m) -
          (δ * (P.lam : R)) • (E P n m * X P n (m+1) false * E P n m) := by
        rw [q]; simp only [add_mul, sub_mul, one_mul, smul_mul_assoc, mul_assoc]
    _ = _ := by
        rw [k0, smul_smul, mul_assoc δ, Units.mul_inv, mul_one]

lemma xinv_e {m : ℕ} (hm : 1 ≤ m) (hmn : m + 2 < n) :
    X P n (m+1) true * E P n (m+2) = X P n (m+2) false * E P n (m+1) * E P n (m+2) := by
  have h := nearL P n (m+1) (m+2) ⟨by omega, by omega⟩ ⟨by omega, hmn⟩ (Or.inl rfl)
  have t2 := tripleE P n (m+2) (m+1) ⟨by omega, hmn⟩ ⟨by omega, by omega⟩ (Or.inr rfl)
  have h2 : X P n (m+1) false * (X P n (m+2) false * E P n (m+1) * E P n (m+2)) = E P n (m+2) := by
    calc X P n (m+1) false * (X P n (m+2) false * E P n (m+1) * E P n (m+2))
        = (X P n (m+1) false * X P n (m+2) false * E P n (m+1)) * E P n (m+2) := by
          simp only [mul_assoc]
      _ = E P n (m+2) := by rw [h, t2]
  have := congrArg (X P n (m+1) true * ·) h2
  simp only [← mul_assoc, xi_x P n (m+1) ⟨by omega, by omega⟩, one_mul] at this
  rw [this]

lemma ac0 (a b l : ℕ) : alphaChain P n a b l 0 =
    intervalProduct (fun t => X P n t false) a b * intervalProduct (E P n) b (l+1) := by
  rw [ac_def, JP_zero, one_mul]

/-- E m * X_{m+1}^{-1} * e_{m+2}..e_l * alpha^0_{m+1,h,l-2} -/
lemma hZlem {m h l : ℕ} (hm : 1 ≤ m) (hmh : m < h) (hhl : h + 2 ≤ l) (hl : l < n) :
    E P n m * (X P n (m+1) true * intervalProduct (E P n) (m+2) (l+1) *
      (intervalProduct (fun t => X P n t false) (m+1) h * intervalProduct (E P n) h (l-1))) =
    intervalProduct (fun t => X P n t false) (m+2) (h+2) * intervalProduct (E P n) (h+2) (l+1) *
      intervalProduct (E P n) m (l-1) := by
  have e1 : intervalProduct (E P n) (m+2) (l+1) = E P n (m+2) * intervalProduct (E P n) (m+3) (l+1) :=
    ip_cons (E P n) (by omega)
  have e2 : intervalProduct (E P n) m (l+1) =
      E P n m * E P n (m+1) * E P n (m+2) * intervalProduct (E P n) (m+3) (l+1) := by
    rw [ip_cons (E P n) (show m < l+1 by omega), ip_cons (E P n) (show m+1 < l+1 by omega),
      ip_cons (E P n) (show m+1+1 < l+1 by omega)]
    simp only [mul_assoc, show m + 1 + 1 + 1 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega]
  have c1 : X P n (m+2) false * E P n m = E P n m * X P n (m+2) false :=
    (cXE P n (a := m+2) (b := m) (by omega) (by omega) hm (by omega) (Or.inr (by omega))).eq
  have hR : intervalProduct (fun t => X P n t false) (m+1) h * intervalProduct (E P n) h (l-1) =
      alphaChain P n (m+1) h (l-2) 0 := by
    rw [ac0, show l - 2 + 1 = l - 1 by omega]
  have hs := shA P n (j := m) (g := m+1) (h := h) (l := l) hm (by omega) (by omega) hhl hl 0
  rw [ac0, ac0, show m + 1 + 2 = m + 3 by omega, show l - 2 + 1 = l - 1 by omega] at hs
  have hab := absorb P n (j := m) (h := h+2) (l := l) hm (by omega) hhl hl
  have hX : X P n (m+2) false * intervalProduct (fun t => X P n t false) (m+3) (h+2) =
      intervalProduct (fun t => X P n t false) (m+2) (h+2) := by
    rw [ip_cons (fun t => X P n t false) (show m+2 < h+2 by omega)]
  calc E P n m * (X P n (m+1) true * intervalProduct (E P n) (m+2) (l+1) *
        (intervalProduct (fun t => X P n t false) (m+1) h * intervalProduct (E P n) h (l-1)))
      = (E P n m * X P n (m+1) true * E P n (m+2)) * intervalProduct (E P n) (m+3) (l+1) *
        (intervalProduct (fun t => X P n t false) (m+1) h * intervalProduct (E P n) h (l-1)) := by
        rw [e1]; simp only [mul_assoc]
    _ = X P n (m+2) false * intervalProduct (E P n) m (l+1) *
        (intervalProduct (fun t => X P n t false) (m+1) h * intervalProduct (E P n) h (l-1)) := by
        rw [mul_assoc (E P n m), xinv_e P n hm (by omega), e2]
        simp only [← mul_assoc]; rw [c1]
    _ = X P n (m+2) false * (intervalProduct (fun t => X P n t false) (m+3) (h+2) *
          (intervalProduct (E P n) (h+2) (l+1) * intervalProduct (E P n) m (l+1))) := by
        rw [mul_assoc (X P n (m+2) false), ← mul_assoc (intervalProduct (E P n) m (l+1)) _ _]
        rw [mul_assoc (intervalProduct (E P n) m (l+1)), hs]; simp only [mul_assoc]
    _ = _ := by
        rw [hab, ← hX]; simp only [mul_assoc]

lemma coreLt {m h l : ℕ} (hm : 1 ≤ m) (hmh : m < h) (hhl : h + 2 ≤ l) (hl : l < n) :
    X P n m false * (intervalProduct (E P n) (m+1) (l+1) * intervalProduct (fun t => X P n t false) m h *
      intervalProduct (E P n) h (l-1)) =
    intervalProduct (fun t => X P n t false) (m+1) (h+2) * intervalProduct (E P n) (h+2) (l+1) *
        intervalProduct (E P n) m (l-1) +
      δ • (intervalProduct (E P n) (m+1) (l+1) * intervalProduct (fun t => X P n t false) m h *
        intervalProduct (E P n) h (l-1)) -
      δ • (intervalProduct (fun t => X P n t false) (m+2) (h+2) * intervalProduct (E P n) (h+2) (l+1) *
        intervalProduct (E P n) m (l-1)) := by
  set Rr := intervalProduct (fun t => X P n t false) (m+1) h * intervalProduct (E P n) h (l-1) with hRr
  set Z := X P n (m+1) true * intervalProduct (E P n) (m+2) (l+1) * Rr with hZ
  have h1 : intervalProduct (fun t => X P n t false) m h =
      X P n m false * intervalProduct (fun t => X P n t false) (m+1) h := ip_cons _ hmh
  have h2 : intervalProduct (E P n) (m+1) (l+1) = E P n (m+1) * intervalProduct (E P n) (m+2) (l+1) :=
    ip_cons (E P n) (show m+1 < l+1 by omega)
  have h3 : Commute (X P n m false) (intervalProduct (E P n) (m+2) (l+1)) :=
    c_ipE P n (fun t h1 h2 => cXE P n hm (by omega) (by omega) (by omega) (Or.inl (by omega)))
  have hQ : intervalProduct (E P n) (m+1) (l+1) * intervalProduct (fun t => X P n t false) m h *
      intervalProduct (E P n) h (l-1) = E P n (m+1) * E P n m * Z := by
    rw [h1, h2, hZ, hRr]
    calc E P n (m+1) * intervalProduct (E P n) (m+2) (l+1) *
          (X P n m false * intervalProduct (fun t => X P n t false) (m+1) h) * intervalProduct (E P n) h (l-1)
        = (E P n (m+1) * X P n m false) * intervalProduct (E P n) (m+2) (l+1) *
          intervalProduct (fun t => X P n t false) (m+1) h * intervalProduct (E P n) h (l-1) := by
          simp only [mul_assoc]
          rw [← mul_assoc (intervalProduct (E P n) (m+2) (l+1)) (X P n m false), ← h3.eq]
          simp only [mul_assoc]
      _ = _ := by rw [eXl P n hm (by omega)]; simp only [mul_assoc]
  have hz := hZlem P n hm hmh hhl hl
  rw [← hRr, ← hZ] at hz
  have hX1 : X P n (m+1) false * intervalProduct (fun t => X P n t false) (m+2) (h+2) =
      intervalProduct (fun t => X P n t false) (m+1) (h+2) := by
    rw [ip_cons (fun t => X P n t false) (show m+1 < h+2 by omega)]
  rw [hQ, ← mul_assoc, K1 P n hm (by omega)]
  simp only [add_mul, sub_mul, smul_mul_assoc]
  rw [mul_assoc (X P n (m+1) false), hz, ← hX1]
  simp only [mul_assoc]

lemma coreEq {m l : ℕ} (hm : 1 ≤ m) (hml : m + 2 ≤ l) (hl : l < n) :
    X P n m false * (intervalProduct (E P n) (m+1) (l+1) * intervalProduct (fun t => X P n t false) m m *
      intervalProduct (E P n) m (l-1)) =
    intervalProduct (fun t => X P n t false) (m+1) (m+2) * intervalProduct (E P n) (m+2) (l+1) *
        intervalProduct (E P n) m (l-1) +
      δ • (intervalProduct (E P n) (m+1) (l+1) * intervalProduct (fun t => X P n t false) m m *
        intervalProduct (E P n) m (l-1)) -
      δ • (intervalProduct (fun t => X P n t false) (m+2) (m+2) * intervalProduct (E P n) (m+2) (l+1) *
        intervalProduct (E P n) m (l-1)) := by
  simp only [ip_self, mul_one, one_mul, ip_one]
  have h2 : intervalProduct (E P n) (m+1) (l+1) = E P n (m+1) * intervalProduct (E P n) (m+2) (l+1) :=
    ip_cons (E P n) (show m+1 < l+1 by omega)
  have h4 : intervalProduct (E P n) m (l-1) = E P n m * intervalProduct (E P n) (m+1) (l-1) :=
    ip_cons (E P n) (show m < l-1 by omega)
  have c : Commute (E P n m) (intervalProduct (E P n) (m+2) (l+1)) :=
    c_ipE P n (fun t h1 h2 => cEE P n hm (by omega) (by omega) (by omega) (Or.inl (by omega)))
  have hQ : intervalProduct (E P n) (m+1) (l+1) * intervalProduct (E P n) m (l-1) =
      E P n (m+1) * E P n m * (intervalProduct (E P n) (m+2) (l+1) * intervalProduct (E P n) (m+1) (l-1)) := by
    rw [h2, h4, mul_assoc (E P n (m+1)), ← mul_assoc _ (E P n m), ← c.eq]; simp only [mul_assoc]
  have hz : E P n m * (intervalProduct (E P n) (m+2) (l+1) * intervalProduct (E P n) (m+1) (l-1)) =
      intervalProduct (E P n) (m+2) (l+1) * intervalProduct (E P n) m (l-1) := by
    rw [h4, ← mul_assoc, c.eq]; simp only [mul_assoc]
  rw [hQ, ← mul_assoc, K1 P n hm (by omega)]
  simp only [add_mul, sub_mul, smul_mul_assoc]
  rw [mul_assoc (X P n (m+1) false), hz]
  simp only [mul_assoc]

end X8L35

end QAlgorithms.Papers.Independent.Gap48.P01

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L35

set_option linter.unusedSectionVars false

open X8L25C X8L33

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

lemma XXgen {i t j : ℕ} (hit : i ≤ t) (htj : t + 2 ≤ j) (y z : NonsplitBMW P n)
    (hfar : Commute y (intervalProduct (fun t => X P n t false) (t+2) j))
    (hlow : Commute z (intervalProduct (fun t => X P n t false) i t))
    (hloc : X P n t false * X P n (t+1) false * y = z * (X P n t false * X P n (t+1) false)) :
    intervalProduct (fun t => X P n t false) i j * y = z * intervalProduct (fun t => X P n t false) i j := by
  have hs : intervalProduct (fun t => X P n t false) i j = intervalProduct (fun t => X P n t false) i t *
      (X P n t false * X P n (t+1) false) * intervalProduct (fun t => X P n t false) (t+2) j := by
    rw [ip_split _ hit (by omega : t ≤ j), ip_cons (fun t => X P n t false) (show t < j by omega),
      ip_cons (fun t => X P n t false) (show t+1 < j by omega)]
    simp only [mul_assoc, show t + 1 + 1 = t + 2 by omega]
  rw [hs]
  calc intervalProduct (fun t => X P n t false) i t * (X P n t false * X P n (t+1) false) *
        intervalProduct (fun t => X P n t false) (t+2) j * y
      = intervalProduct (fun t => X P n t false) i t * (X P n t false * X P n (t+1) false * y) *
        intervalProduct (fun t => X P n t false) (t+2) j := by
        rw [mul_assoc _ _ y, ← hfar.eq]; simp only [mul_assoc]
    _ = _ := by rw [hloc, ← mul_assoc, ← hlow.eq]; simp only [mul_assoc]

lemma XXx {i t j : ℕ} (hi : 1 ≤ i) (hit : i ≤ t) (htj : t + 2 ≤ j) (hj : j ≤ n) :
    intervalProduct (fun t => X P n t false) i j * X P n t false =
      X P n (t+1) false * intervalProduct (fun t => X P n t false) i j :=
  XXgen P n hit htj _ _
    (c_ipX P n (fun s h1 h2 => cXX P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))))
    (c_ipX P n (fun s h1 h2 => cXX P n (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))))
    (by have := braid P n t ⟨by omega, by omega⟩; simpa only [mul_assoc] using this)

lemma XXe {i t j : ℕ} (hi : 1 ≤ i) (hit : i ≤ t) (htj : t + 2 ≤ j) (hj : j ≤ n) :
    intervalProduct (fun t => X P n t false) i j * E P n t =
      E P n (t+1) * intervalProduct (fun t => X P n t false) i j :=
  XXgen P n hit htj _ _
    (c_ipX P n (fun s h1 h2 => (cXE P n (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))).symm))
    (c_ipX P n (fun s h1 h2 => (cXE P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))).symm))
    (by rw [nearL P n t (t+1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inl rfl), ← mul_assoc,
          nearR P n t (t+1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inl rfl)])

/-- X_t alpha^0_{i,t,l-2} = alpha^0_{i,t-1,l-2} -/
lemma Xdown {i t l : ℕ} (hi : 1 ≤ i) (hit : i < t) (htl : t + 2 ≤ l) (hl : l < n) :
    X P n t false * (intervalProduct (fun t => X P n t false) i t * intervalProduct (E P n) t (l-1)) =
      intervalProduct (fun t => X P n t false) i (t-1) * intervalProduct (E P n) (t-1) (l-1) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have c : Commute (X P n (s+1) false) (intervalProduct (fun t => X P n t false) i s) :=
    c_ipX P n (fun u h1 h2 => cXX P n (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)))
  have nl := nearL P n (s+1) s ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr rfl)
  rw [ip_snoc _ (by omega : i ≤ s), ip_cons (E P n) (show s < l - 1 by omega),
    ip_cons (E P n) (show s + 1 < l - 1 by omega)]
  calc X P n (s+1) false * (intervalProduct (fun t => X P n t false) i s * X P n s false *
        (E P n (s+1) * intervalProduct (E P n) (s+1+1) (l-1)))
      = intervalProduct (fun t => X P n t false) i s * (X P n (s+1) false * X P n s false * E P n (s+1)) *
        intervalProduct (E P n) (s+1+1) (l-1) := by
        simp only [← mul_assoc]; rw [c.eq]
    _ = _ := by rw [nl]; simp only [mul_assoc]

lemma Ldown {i g l : ℕ} (hi : 1 ≤ i) (hig : i ≤ g) (hl : l < n) : ∀ t, g ≤ t → t + 2 ≤ l →
    intervalProduct (fun t => X P n t false) (g+1) (t+1) *
      (intervalProduct (fun t => X P n t false) i t * intervalProduct (E P n) t (l-1)) =
    intervalProduct (fun t => X P n t false) i g * intervalProduct (E P n) g (l-1) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => intro _; rw [ip_self, one_mul]
  | succ t ht ih =>
    intro htl
    rw [ip_snoc _ (by omega : g + 1 ≤ t + 1), mul_assoc, Xdown P n hi (by omega) htl hl,
      Nat.add_sub_cancel, ih (by omega)]

end X8L35

end QAlgorithms.Papers.Independent.Gap48.P01

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L35

set_option linter.unusedSectionVars false

open X8L25C X8L33

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

local notation "δ" => skeinDelta P

lemma ip_shift1 {M : Type*} [Monoid M] (a : ℕ → M) (c : M) {s u : ℕ} (hsu : s ≤ u)
    (h : ∀ t, s ≤ t → t < u → c * a t = a (t+1) * c) :
    c * intervalProduct a s u = intervalProduct a (s+1) (u+1) * c := by
  induction u, hsu using Nat.le_induction with
  | base => simp [ip_self]
  | succ u hu ih =>
    rw [ip_snoc _ hu, ip_snoc _ (by omega : s + 1 ≤ u + 1),
      ← mul_assoc, ih (fun t h1 h2 => h t h1 (by omega)), mul_assoc, h u hu (by omega), ← mul_assoc]

lemma cXXip {a b c d : ℕ} (ha : 1 ≤ a) (hc : 1 ≤ c) (hb : b ≤ n) (hd : d ≤ n)
    (h : b + 1 ≤ c ∨ d + 1 ≤ a) :
    Commute (intervalProduct (fun t => X P n t false) a b) (intervalProduct (fun t => X P n t false) c d) :=
  ip_comm _ _ (fun t h1 h2 => c_ipX P n (fun s h3 h4 =>
    cXX P n (by omega) (by omega) (by omega) (by omega) (by omega)))

lemma cXEip {a b c d : ℕ} (ha : 1 ≤ a) (hc : 1 ≤ c) (hb : b ≤ n) (hd : d ≤ n)
    (h : b + 1 ≤ c ∨ d + 1 ≤ a) :
    Commute (intervalProduct (fun t => X P n t false) a b) (intervalProduct (E P n) c d) :=
  ip_comm _ _ (fun t h1 h2 => c_ipE P n (fun s h3 h4 =>
    cXE P n (by omega) (by omega) (by omega) (by omega) (by omega)))

lemma cEEip {a b c d : ℕ} (ha : 1 ≤ a) (hc : 1 ≤ c) (hb : b ≤ n) (hd : d ≤ n)
    (h : b + 1 ≤ c ∨ d + 1 ≤ a) :
    Commute (intervalProduct (E P n) a b) (intervalProduct (E P n) c d) :=
  ip_comm _ _ (fun t h1 h2 => c_ipE P n (fun s h3 h4 =>
    cEE P n (by omega) (by omega) (by omega) (by omega) (by omega)))

/-- JP_c commutes with chains starting above c. -/
lemma cJa {c a b l : ℕ} (hc : 1 ≤ c) (hca : c < a) (hab : a ≤ b) (hbl : b ≤ l) (hl : l < n) (s p : ℤ) :
    Commute (JPower P n c s) (alphaChain P n a b l p) := by
  rw [ac_def]
  refine ((cJJ' P n hc hca (by omega) s p).mul_right ?_).mul_right ?_
  · exact c_ipX P n (fun t h1 h2 => cJX_hi P n hc (by omega) (by omega) s)
  · exact c_ipE P n (fun t h1 h2 => cJE_hi P n hc (by omega) (by omega) s)

/-- ipX(i,g) commutes with chains starting at ≥ g+1. -/
lemma cXa {i g a b l : ℕ} (hi : 1 ≤ i) (hga : g + 1 ≤ a) (hab : a ≤ b) (hbl : b ≤ l) (hl : l < n) (p : ℤ) :
    Commute (intervalProduct (fun t => X P n t false) i g) (alphaChain P n a b l p) := by
  apply ip_comm
  intro t ht1 ht2
  rw [ac_def]
  refine ((cJX_lo P n (by omega) (by omega) (by omega) p).symm.mul_right ?_).mul_right ?_
  · exact c_ipX P n (fun s hs1 hs2 => cXX P n (a := t) (b := s) (by omega) (by omega) (by omega)
      (by omega) (Or.inl (by omega)))
  · exact c_ipE P n (fun s hs1 hs2 => cXE P n (a := t) (b := s) (by omega) (by omega) (by omega)
      (by omega) (Or.inl (by omega)))

lemma JPa (a b l : ℕ) (r : ℤ) : JPower P n a r * alphaChain P n a b l 0 = alphaChain P n a b l r := by
  rw [ac_def, ac_def, JP_zero, one_mul]; simp only [mul_assoc]

/-- identity (*): ipX(i,c+2) e_{c+2}..e_l · e_c..e_{l-2} = e_{c+1}..e_l · ipX(i,c) e_c..e_{l-2} -/
lemma star {i c l : ℕ} (hi : 1 ≤ i) (hic : i ≤ c) (hcl : c + 2 ≤ l) (hl : l < n) :
    intervalProduct (fun t => X P n t false) i (c+2) * intervalProduct (E P n) (c+2) (l+1) *
      intervalProduct (E P n) c (l-1) =
    intervalProduct (E P n) (c+1) (l+1) * (intervalProduct (fun t => X P n t false) i c *
      intervalProduct (E P n) c (l-1)) := by
  have hX : intervalProduct (fun t => X P n t false) i (c+2) =
      intervalProduct (fun t => X P n t false) i c * (X P n c false * X P n (c+1) false) := by
    rw [ip_snoc _ (by omega : i ≤ c + 1), ip_snoc _ hic]; simp only [mul_assoc]
  have hE : intervalProduct (E P n) c (l-1) = E P n c * intervalProduct (E P n) (c+1) (l-1) :=
    ip_cons _ (by omega)
  have hE2 : intervalProduct (E P n) (c+1) (l+1) = E P n (c+1) * intervalProduct (E P n) (c+2) (l+1) :=
    ip_cons _ (by omega)
  have cm : Commute (intervalProduct (E P n) (c+2) (l+1)) (E P n c) :=
    (c_ipE P n (fun t h1 h2 => cEE P n (a := c) (b := t) (by omega) (by omega) (by omega) (by omega)
      (Or.inl (by omega)))).symm
  have nl := nearL P n c (c+1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inl rfl)
  have cX : Commute (intervalProduct (fun t => X P n t false) i c) (intervalProduct (E P n) (c+1) (l+1)) :=
    cXEip P n hi (by omega) (by omega) (by omega) (Or.inl (by omega))
  rw [hX, hE]
  calc intervalProduct (fun t => X P n t false) i c * (X P n c false * X P n (c+1) false) *
        intervalProduct (E P n) (c+2) (l+1) * (E P n c * intervalProduct (E P n) (c+1) (l-1))
      = intervalProduct (fun t => X P n t false) i c * (X P n c false * X P n (c+1) false *
        (intervalProduct (E P n) (c+2) (l+1) * E P n c)) * intervalProduct (E P n) (c+1) (l-1) := by
        simp only [mul_assoc]
    _ = intervalProduct (fun t => X P n t false) i c * (X P n c false * X P n (c+1) false * E P n c) *
        intervalProduct (E P n) (c+2) (l+1) * intervalProduct (E P n) (c+1) (l-1) := by
        rw [cm.eq]; simp only [mul_assoc]
    _ = intervalProduct (fun t => X P n t false) i c * intervalProduct (E P n) (c+1) (l+1) *
        (E P n c * intervalProduct (E P n) (c+1) (l-1)) := by
        rw [nl, hE2]; simp only [mul_assoc]
        rw [← mul_assoc (E P n c) (intervalProduct (E P n) (c+2) (l+1)), ← cm.eq, mul_assoc]
    _ = _ := by rw [cX.eq]; simp only [mul_assoc]

/-- Term 1, subcase h ≤ j-2, exponent zero. -/
lemma id1z {i j g h l : ℕ} (hl : l < n) (hi : 1 ≤ i) (hig : i ≤ g) (hgh : g ≤ h) (hhj : h + 2 ≤ j)
    (hjl : j ≤ l) :
    alphaChain P n i j l 0 * alphaChain P n g h (l-2) 0 =
      alphaChain P n (g+1) (h+1) l 0 * alphaChain P n i (j-2) (l-2) 0 := by
  obtain ⟨c, rfl⟩ : ∃ c, j = c + 2 := ⟨j - 2, by omega⟩
  simp only [ac0, show l - 2 + 1 = l - 1 by omega, Nat.add_sub_cancel]
  -- step a: e_j..e_l past ipX(g,h)
  have ca : Commute (intervalProduct (E P n) (c+2) (l+1)) (intervalProduct (fun t => X P n t false) g h) :=
    (cXEip P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))).symm
  -- step b
  have sb : intervalProduct (fun t => X P n t false) i (c+2) * intervalProduct (fun t => X P n t false) g h =
      intervalProduct (fun t => X P n t false) (g+1) (h+1) * intervalProduct (fun t => X P n t false) i (c+2) :=
    ip_shift1 _ _ hgh (fun t h1 h2 => XXx P n hi (by omega) (by omega) (by omega))
  -- step c
  have sc : intervalProduct (E P n) h (l-1) = intervalProduct (E P n) h c * intervalProduct (E P n) c (l-1) :=
    ip_split _ (by omega) (by omega)
  have cd : Commute (intervalProduct (E P n) (c+2) (l+1)) (intervalProduct (E P n) h c) :=
    cEEip P n (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
  have se : intervalProduct (fun t => X P n t false) i (c+2) * intervalProduct (E P n) h c =
      intervalProduct (E P n) (h+1) (c+1) * intervalProduct (fun t => X P n t false) i (c+2) :=
    ip_shift1 _ _ (by omega) (fun t h1 h2 => XXe P n hi (by omega) (by omega) (by omega))
  have sf := star P n hi (by omega : i ≤ c) (by omega) hl
  have sp1 : intervalProduct (fun t => X P n t false) (g+1) (h+1) * intervalProduct (E P n) (h+1) (l+1) =
      intervalProduct (fun t => X P n t false) (g+1) (h+1) * intervalProduct (E P n) (h+1) (c+1) *
        intervalProduct (E P n) (c+1) (l+1) := by
    rw [ip_split (E P n) (by omega : h + 1 ≤ c + 1) (by omega : c + 1 ≤ l + 1)]; simp only [mul_assoc]
  rw [sp1, sc]
  calc intervalProduct (fun t => X P n t false) i (c+2) * intervalProduct (E P n) (c+2) (l+1) *
        (intervalProduct (fun t => X P n t false) g h * (intervalProduct (E P n) h c *
          intervalProduct (E P n) c (l-1)))
      = (intervalProduct (fun t => X P n t false) i (c+2) * intervalProduct (fun t => X P n t false) g h) *
        intervalProduct (E P n) (c+2) (l+1) * intervalProduct (E P n) h c *
          intervalProduct (E P n) c (l-1) := by
        rw [mul_assoc _ (intervalProduct (E P n) (c+2) (l+1)), ← mul_assoc (intervalProduct (E P n) (c+2) (l+1)),
          ca.eq]; simp only [mul_assoc]
    _ = intervalProduct (fun t => X P n t false) (g+1) (h+1) *
        (intervalProduct (fun t => X P n t false) i (c+2) * intervalProduct (E P n) h c) *
        intervalProduct (E P n) (c+2) (l+1) * intervalProduct (E P n) c (l-1) := by
        rw [sb, mul_assoc _ (intervalProduct (E P n) (c+2) (l+1)), cd.eq]; simp only [mul_assoc]
    _ = _ := by
        rw [se]; simp only [mul_assoc] at sf ⊢
        rw [sf]

lemma hJ {i a b c l : ℕ} (hi : 1 ≤ i) (hia : i < a) (hab : a ≤ b) (hbl : b ≤ l) (hl : l < n) (p : ℤ) :
    JPower P n i p * (alphaChain P n a b l 0 * alphaChain P n i c (l-2) 0) =
      alphaChain P n a b l 0 * alphaChain P n i c (l-2) p := by
  rw [← mul_assoc, (cJa P n hi hia hab hbl hl p 0).eq, mul_assoc, JPa]

lemma id1 {i j g h l : ℕ} (hl : l < n) (hi : 1 ≤ i) (hig : i ≤ g) (hgh : g ≤ h) (hhj : h + 2 ≤ j)
    (hjl : j ≤ l) (p : ℤ) :
    alphaChain P n i j l p * alphaChain P n g h (l-2) 0 =
      alphaChain P n (g+1) (h+1) l 0 * alphaChain P n i (j-2) (l-2) p := by
  rw [← JPa P n i j l p, mul_assoc, id1z P n hl hi hig hgh hhj hjl,
    hJ P n hi (by omega) (by omega) (by omega) hl]

lemma core {m h l : ℕ} (hm : 1 ≤ m) (hmh : m ≤ h) (hhl : h + 2 ≤ l) (hl : l < n) :
    X P n m false * (intervalProduct (E P n) (m+1) (l+1) * intervalProduct (fun t => X P n t false) m h *
      intervalProduct (E P n) h (l-1)) =
    intervalProduct (fun t => X P n t false) (m+1) (h+2) * intervalProduct (E P n) (h+2) (l+1) *
        intervalProduct (E P n) m (l-1) +
      δ • (intervalProduct (E P n) (m+1) (l+1) * intervalProduct (fun t => X P n t false) m h *
        intervalProduct (E P n) h (l-1)) -
      δ • (intervalProduct (fun t => X P n t false) (m+2) (h+2) * intervalProduct (E P n) (h+2) (l+1) *
        intervalProduct (E P n) m (l-1)) := by
  rcases lt_or_eq_of_le hmh with h1 | rfl
  · exact coreLt P n hm h1 hhl hl
  · exact coreEq P n hm hhl hl

/-- Term 1, subcase h ≥ j-1 (j = m+1), exponent zero. -/
lemma id2z {i m g h l : ℕ} (hl : l < n) (hi : 1 ≤ i) (hig : i ≤ g) (hgm : g ≤ m) (hmh : m ≤ h)
    (hhl : h + 2 ≤ l) :
    alphaChain P n i (m+1) l 0 * alphaChain P n g h (l-2) 0 =
      alphaChain P n (g+1) (h+2) l 0 * alphaChain P n i m (l-2) 0 +
      δ • (alphaChain P n (g+1) (m+1) l 0 * alphaChain P n i h (l-2) 0) -
      δ • (alphaChain P n (m+2) (h+2) l 0 * alphaChain P n i g (l-2) 0) := by
  have hm : 1 ≤ m := by omega
  have c1 : Commute (intervalProduct (E P n) (m+1) (l+1)) (intervalProduct (fun t => X P n t false) g m) :=
    (cXEip P n (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))).symm
  have s2 : intervalProduct (fun t => X P n t false) i m * X P n m false *
      intervalProduct (fun t => X P n t false) g m =
      intervalProduct (fun t => X P n t false) (g+1) (m+1) *
        (intervalProduct (fun t => X P n t false) i m * X P n m false) := by
    rw [← ip_snoc _ (by omega : i ≤ m)]
    exact ip_shift1 _ _ hgm (fun t h1 h2 => XXx P n hi (by omega) (by omega) (by omega))
  have s2r : ∀ z, intervalProduct (fun t => X P n t false) i m * (X P n m false *
      (intervalProduct (fun t => X P n t false) g m * z)) =
      intervalProduct (fun t => X P n t false) (g+1) (m+1) *
        (intervalProduct (fun t => X P n t false) i m * (X P n m false * z)) := by
    intro z; simp only [← mul_assoc]; rw [s2]; simp only [mul_assoc]
  have eL : alphaChain P n i (m+1) l 0 * alphaChain P n g h (l-2) 0 =
      intervalProduct (fun t => X P n t false) (g+1) (m+1) *
        (intervalProduct (fun t => X P n t false) i m * (X P n m false *
          (intervalProduct (E P n) (m+1) (l+1) * intervalProduct (fun t => X P n t false) m h *
            intervalProduct (E P n) h (l-1)))) := by
    simp only [ac0, show l - 2 + 1 = l - 1 by omega]
    rw [ip_split (fun t => X P n t false) (by omega : g ≤ m) (by omega : m ≤ h),
      ip_snoc (fun t => X P n t false) (by omega : i ≤ m)]
    simp only [mul_assoc]
    rw [c1.left_comm, s2r]
  have eA : intervalProduct (fun t => X P n t false) (g+1) (m+1) *
      (intervalProduct (fun t => X P n t false) i m *
        (intervalProduct (fun t => X P n t false) (m+1) (h+2) * intervalProduct (E P n) (h+2) (l+1) *
          intervalProduct (E P n) m (l-1))) =
      alphaChain P n (g+1) (h+2) l 0 * alphaChain P n i m (l-2) 0 := by
    simp only [ac0, show l - 2 + 1 = l - 1 by omega]
    have cA1 := cXXip P n (a := i) (b := m) (c := m+1) (d := h+2) hi (by omega) (by omega) (by omega)
      (Or.inl le_rfl)
    have cA2 := cXEip P n (a := i) (b := m) (c := h+2) (d := l+1) hi (by omega) (by omega) (by omega)
      (Or.inl (by omega))
    simp only [mul_assoc]
    rw [cA1.left_comm, cA2.left_comm, ← mul_assoc (intervalProduct (fun t => X P n t false) (g+1) (m+1)),
      ← ip_split _ (by omega : g + 1 ≤ m + 1) (by omega : m + 1 ≤ h + 2)]
  have eB : intervalProduct (fun t => X P n t false) (g+1) (m+1) *
      (intervalProduct (fun t => X P n t false) i m *
        (intervalProduct (E P n) (m+1) (l+1) * intervalProduct (fun t => X P n t false) m h *
          intervalProduct (E P n) h (l-1))) =
      alphaChain P n (g+1) (m+1) l 0 * alphaChain P n i h (l-2) 0 := by
    simp only [ac0, show l - 2 + 1 = l - 1 by omega]
    have cB := cXEip P n (a := i) (b := m) (c := m+1) (d := l+1) hi (by omega) (by omega) (by omega)
      (Or.inl le_rfl)
    simp only [mul_assoc]
    rw [cB.left_comm, ← mul_assoc (intervalProduct (fun t => X P n t false) i m),
      ← ip_split _ (by omega : i ≤ m) hmh]
  have eC : intervalProduct (fun t => X P n t false) (g+1) (m+1) *
      (intervalProduct (fun t => X P n t false) i m *
        (intervalProduct (fun t => X P n t false) (m+2) (h+2) * intervalProduct (E P n) (h+2) (l+1) *
          intervalProduct (E P n) m (l-1))) =
      alphaChain P n (m+2) (h+2) l 0 * alphaChain P n i g (l-2) 0 := by
    simp only [ac0, show l - 2 + 1 = l - 1 by omega]
    have c1 := cXXip P n (a := i) (b := m) (c := m+2) (d := h+2) hi (by omega) (by omega) (by omega)
      (Or.inl (by omega))
    have c2 := cXEip P n (a := i) (b := m) (c := h+2) (d := l+1) hi (by omega) (by omega) (by omega)
      (Or.inl (by omega))
    have c3 := cXXip P n (a := g+1) (b := m+1) (c := m+2) (d := h+2) (by omega) (by omega) (by omega)
      (by omega) (Or.inl le_rfl)
    have c4 := cXEip P n (a := g+1) (b := m+1) (c := h+2) (d := l+1) (by omega) (by omega) (by omega)
      (by omega) (Or.inl (by omega))
    simp only [mul_assoc]
    rw [c1.left_comm, c2.left_comm, c3.left_comm, c4.left_comm,
      Ldown P n hi hig hl m hgm (by omega)]
  rw [eL, core P n hm hmh hhl hl, mul_sub, mul_add, mul_sub, mul_add, mul_smul_comm, mul_smul_comm,
    mul_smul_comm, mul_smul_comm, eA, eB, eC]

lemma id2 {i m g h l : ℕ} (hl : l < n) (hi : 1 ≤ i) (hig : i ≤ g) (hgm : g ≤ m) (hmh : m ≤ h)
    (hhl : h + 2 ≤ l) (p : ℤ) :
    alphaChain P n i (m+1) l p * alphaChain P n g h (l-2) 0 =
      alphaChain P n (g+1) (h+2) l 0 * alphaChain P n i m (l-2) p +
      δ • (alphaChain P n (g+1) (m+1) l 0 * alphaChain P n i h (l-2) p) -
      δ • (alphaChain P n (m+2) (h+2) l 0 * alphaChain P n i g (l-2) p) := by
  rw [← JPa P n i (m+1) l p, mul_assoc, id2z P n hl hi hig hgm hmh hhl, mul_sub, mul_add,
    mul_smul_comm, mul_smul_comm, hJ P n hi (by omega) (by omega) (by omega) hl,
    hJ P n hi (by omega) (by omega) (by omega) hl, hJ P n hi (by omega) (by omega) (by omega) hl]

end X8L35

end QAlgorithms.Papers.Independent.Gap48.P01

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L35

set_option linter.unusedSectionVars false

open X8L25C X8L33

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

local notation "δ" => skeinDelta P

def Tset (l i : ℕ) : Submodule R (NonsplitBMW P n) := Submodule.span R
  {z | ∃ ip jp gp hh : ℕ, ∃ pp rr : ℤ,
    1 ≤ ip ∧ ip ≤ jp ∧ jp ≤ l ∧ i < ip ∧
    1 ≤ gp ∧ gp ≤ hh ∧ hh ≤ l-2 ∧ exponentRange k pp ∧ exponentRange k rr ∧
    ∃ b ∈ level P n (l-3),
      z = alphaChain P n ip jp l pp * alphaChain P n gp hh (l-2) rr * b}

def L2 (l : ℕ) : Submodule R (NonsplitBMW P n) :=
  alphaSpan P n (l-2) (fun _ p => -(((k-1)/2 : ℕ) : ℤ) ≤ p ∧ p ≤ (k:ℤ) - ((k-1)/2 : ℕ) - 1)

def Lp (l g : ℕ) : Submodule R (NonsplitBMW P n) :=
  alphaSpan P n (l-2) (fun g' p' => g ≤ g' ∧ |p'| ≤ (((k-1)/2 : ℕ) : ℤ))

lemma pr_of {p : ℤ} (hk : 0 < k) : exponentRange k p ↔
    (-(((k-1)/2 : ℕ) : ℤ) ≤ p ∧ p ≤ (k:ℤ) - ((k-1)/2 : ℕ) - 1) := by
  unfold exponentRange; omega

lemma pr_abs {p : ℤ} (hk : 0 < k) (h : |p| ≤ (((k-1)/2 : ℕ) : ℤ)) : exponentRange k p := by
  rw [abs_le] at h; unfold exponentRange; omega

lemma pr_zero (hk : 0 < k) : exponentRange k 0 := by unfold exponentRange; omega

lemma L2_left {l : ℕ} (h3 : 3 ≤ l) (hl : l < n) :
    ∀ x ∈ level P n (l-1), ∀ y ∈ L2 P n l, x * y ∈ L2 P n l := by
  have := lemma_3_4 P n (l-2) ((k-1)/2) (by omega) (by omega) (by have := P.positive; omega)
  rw [show l - 2 + 1 = l - 1 by omega] at this
  exact fun x hx y hy => this.2 x hx y hy

lemma L2_mem {l g h : ℕ} {r : ℤ} {b : NonsplitBMW P n} (hg : 1 ≤ g) (hgh : g ≤ h) (hh : h ≤ l-2)
    (hr : exponentRange k r) (hb : b ∈ level P n (l-3)) :
    alphaChain P n g h (l-2) r * b ∈ L2 P n l :=
  as_mem P n g h r hg hgh hh ((pr_of P.positive).1 hr)
    (by rwa [show l - 2 - 1 = l - 3 by omega])

lemma toT {l i ip jp : ℕ} {pp : ℤ} (h3 : 3 ≤ l) (hl : l < n) (h1 : 1 ≤ ip) (h2 : ip ≤ jp)
    (h4 : jp ≤ l) (hi : i < ip) (hpp : exponentRange k pp) {x y : NonsplitBMW P n}
    (hx : x ∈ level P n (l-1)) (hy : y ∈ L2 P n l) :
    alphaChain P n ip jp l pp * x * y ∈ Tset P n l i := by
  rw [mul_assoc]
  have hxy := L2_left P n h3 hl x hx y hy
  have hle : L2 P n l ≤ (Tset P n l i).comap (LinearMap.mulLeft R (alphaChain P n ip jp l pp)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g', h', r', hg1, hg2, hg3, hF, b, hb, rfl⟩
    show alphaChain P n ip jp l pp * (alphaChain P n g' h' (l-2) r' * b) ∈ Tset P n l i
    rw [← mul_assoc]
    exact Submodule.subset_span ⟨ip, jp, g', h', pp, r', h1, h2, h4, hi, hg1, hg2, hg3, hpp,
      (pr_of P.positive).2 hF, b, by rwa [show l - 2 - 1 = l - 3 by omega] at hb, rfl⟩
  exact hle hxy

lemma Lp_gen {l g t : ℕ} (hl : l < n) (h3 : 3 ≤ l) (hg : 1 ≤ g) (hgt : g ≤ t) (htl : t ≤ l-2)
    (f : ℕ → NonsplitBMW P n) (hf : f = (fun t => X P n t false) ∨ f = E P n) :
    ∀ z ∈ Lp P n l g, f t * z ∈ Lp P n l g := by
  intro z hz
  have hle : Lp P n l g ≤ (Lp P n l g).comap (LinearMap.mulLeft R (f t)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g', h', p', hg1, hg2, hg3, hF, b, hb, rfl⟩
    show f t * (alphaChain P n g' h' (l-2) p' * b) ∈ Lp P n l g
    have h := x8_main33 P n (l-2) g' h' t (by omega) hg1 hg2 hg3 (by omega) htl p' f hf
    have h' := as_mul P n (as_mono P n (G := fun g' p' => g ≤ g' ∧ |p'| ≤ (((k-1)/2 : ℕ) : ℤ))
      (fun ip pp hh => ⟨le_trans (le_min hF.1 hgt) hh.1, le_trans hh.2.1 hF.2⟩) h) hb
    rw [mul_assoc] at h'
    exact h'
  exact hle hz

lemma Lp_Xi {l g t : ℕ} (hl : l < n) (h3 : 3 ≤ l) (hg : 1 ≤ g) (hgt : g ≤ t) (htl : t ≤ l-2) :
    ∀ z ∈ Lp P n l g, X P n t true * z ∈ Lp P n l g := by
  intro z hz
  have e : X P n t true = X P n t false - δ • (1 - E P n t) := by
    rw [← skein P n t ⟨by omega, by omega⟩]; abel
  have hX := Lp_gen P n hl h3 hg hgt htl _ (Or.inl rfl) z hz
  have hE := Lp_gen P n hl h3 hg hgt htl _ (Or.inr rfl) z hz
  rw [e, sub_mul, smul_mul_assoc, sub_mul, one_mul]
  exact sub_mem hX (Submodule.smul_mem _ _ (sub_mem hz hE))

lemma Lp_Wv {l g : ℕ} (hl : l < n) (h3 : 3 ≤ l) (hg : 1 ≤ g) :
    ∀ d, g + d ≤ l - 1 → ∀ z ∈ Lp P n l g, Wv P n g d * z ∈ Lp P n l g := by
  intro d
  induction d with
  | zero => intro _ z hz; simpa [Wv] using hz
  | succ d ih =>
    intro hd z hz
    show X P n (g+d) true * Wv P n g d * z ∈ Lp P n l g
    rw [mul_assoc]
    exact Lp_Xi P n hl h3 hg (by omega) (by omega) _ (ih (by omega) z hz)

/-- Term 3 core: W v^s e_g..e_l z ∈ T for z ∈ L'. -/
lemma T3gen {l i g : ℕ} (hl : l < n) (h3 : 3 ≤ l) (hi : 1 ≤ i) (hig : i ≤ g) (hgl : g + 2 ≤ l)
    (p s : ℤ) : ∀ z ∈ Lp P n l g,
    JPower P n i p * intervalProduct (fun t => X P n t false) i g * JPower P n (g+1) s *
      intervalProduct (E P n) g (l+1) * z ∈ Tset P n l i := by
  intro z hz
  set a := JPower P n i p * intervalProduct (fun t => X P n t false) i g * JPower P n (g+1) s with ha
  have hle : Lp P n l g ≤ (Tset P n l i).comap
      (LinearMap.mulLeft R (a * intervalProduct (E P n) g (l+1))) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g', h', p', hg1, hg2, hg3, hF, b, hb, rfl⟩
    show a * intervalProduct (E P n) g (l+1) * (alphaChain P n g' h' (l-2) p' * b) ∈ Tset P n l i
    have e0 := absorb P n (j := g) (h := h'+2) (l := l) (by omega) (by omega) (by omega) hl
    have e1 : intervalProduct (E P n) g (l+1) * alphaChain P n g' h' (l-2) p' =
        alphaChain P n (g'+2) (h'+2) l p' * intervalProduct (E P n) g (l-1) := by
      rw [shA P n (by omega) hF.1 hg2 (by omega) hl]
      simp only [ac_def, mul_assoc]; rw [e0]
    have c : Commute a (alphaChain P n (g'+2) (h'+2) l p') := by
      rw [ha]
      exact (((cJa P n hi (by omega) (by omega) (by omega) hl p p').mul_left
        (cXa P n hi (by omega) (by omega) (by omega) hl p')).mul_left
        (cJa P n (by omega) (by omega) (by omega) (by omega) hl s p'))
    have e2 : intervalProduct (E P n) g (l-1) = alphaChain P n g g (l-2) 0 := by
      rw [ac00, show l - 2 + 1 = l - 1 by omega]
    have hx : a ∈ level P n (l-1) := by
      rw [ha]
      exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (lv_JP P n hi (by omega) p)
        (lv_ipX P n hi (by omega))) (lv_JP P n (by omega) (by omega) s)
    have hy : alphaChain P n g g (l-2) 0 * b ∈ L2 P n l :=
      L2_mem P n (by omega) le_rfl (by omega) (pr_zero P.positive)
        (by rwa [show l - 2 - 1 = l - 3 by omega] at hb)
    have := toT P n (l := l) (i := i) h3 hl (ip := g'+2) (jp := h'+2) (by omega) (by omega) (by omega) (by omega)
      (pr_abs P.positive hF.2) hx hy
    have eq : a * intervalProduct (E P n) g (l+1) * (alphaChain P n g' h' (l-2) p' * b)
        = alphaChain P n (g'+2) (h'+2) l p' * a * (alphaChain P n g g (l-2) 0 * b) := by
      calc a * intervalProduct (E P n) g (l+1) * (alphaChain P n g' h' (l-2) p' * b)
          = a * (intervalProduct (E P n) g (l+1) * alphaChain P n g' h' (l-2) p') * b := by
            simp only [mul_assoc]
        _ = alphaChain P n (g'+2) (h'+2) l p' * a * (alphaChain P n g g (l-2) 0 * b) := by
            rw [e1, ← e2, ← mul_assoc, c.eq]; simp only [mul_assoc]
    rw [eq]; exact this
  exact hle hz

end X8L35

end QAlgorithms.Papers.Independent.Gap48.P01

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8L35

set_option linter.unusedSectionVars false

open X8L25C X8L33

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

local notation "δ" => skeinDelta P

lemma L2_mem1 {l g h : ℕ} {r : ℤ} (hg : 1 ≤ g) (hgh : g ≤ h) (hh : h ≤ l-2)
    (hr : exponentRange k r) : alphaChain P n g h (l-2) r ∈ L2 P n l :=
  as_mem1 P n g h r hg hgh hh ((pr_of P.positive).1 hr)

theorem main35 (l i j g h : ℕ) (hl : l < n)
    (hi : 1 ≤ i) (hij : i ≤ j) (hjl : j ≤ l)
    (hg : 1 ≤ g) (hgh : g ≤ h) (hhl : h ≤ l-2) (hig : i ≤ g)
    (p r : ℤ) (hp : exponentRange k p) (hr : exponentRange k r) :
    alphaChain P n i j l p * alphaChain P n g h (l-2) r ∈ Tset P n l i := by
  have h3 : 3 ≤ l := by omega
  have hk := P.positive
  by_cases hgj : j ≤ g
  · rw [caseGJ P n hl hi hij hgj hgh (by omega) p r]
    have := toT P n (l := l) (i := i) h3 hl (ip := g+2) (jp := h+2) (by omega) (by omega) (by omega)
      (by omega) hr (Subalgebra.one_mem _) (L2_mem1 P n hi hij (by omega) hp)
    simpa only [mul_one] using this
  push_neg at hgj
  obtain ⟨W, hW⟩ : ∃ W, W = JPower P n i p * intervalProduct (fun t => X P n t false) i g := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = intervalProduct (fun t => X P n t false) (g+1) j *
      intervalProduct (E P n) j (l+1) := ⟨_, rfl⟩
  obtain ⟨A0, hA0⟩ : ∃ A0, A0 = alphaChain P n g h (l-2) 0 := ⟨_, rfl⟩
  have hA : alphaChain P n i j l p = W * X P n g false * C := by
    rw [hW, hC, ac_def, ip_split (fun t => X P n t false) hig (le_of_lt hgj),
      ip_cons (fun t => X P n t false) hgj]
    simp only [mul_assoc]
  have hCu : ∀ a, Commute (JPower P n g a) C := by
    intro a; rw [hC]
    exact (c_ipX P n (fun t h1 h2 => cJX_hi P n hg (by omega) (by omega) a)).mul_right
      (c_ipE P n (fun t h1 h2 => cJE_hi P n hg (by omega) (by omega) a))
  have hWv : ∀ s, Commute W (JPower P n (g+1) s) := by
    intro s; rw [hW]
    exact (cJJ' P n hi (by omega) (by omega) p s).mul_left
      (ip_comm _ _ (fun t h1 h2 => (cJX_lo P n (by omega) (by omega) (by omega) s).symm))
  have hWC : Commute W C := by
    rw [hW, hC]
    refine Commute.mul_left ?_ ?_
    · exact (c_ipX P n (fun t h1 h2 => cJX_hi P n hi (by omega) (by omega) p)).mul_right
        (c_ipE P n (fun t h1 h2 => cJE_hi P n hi (by omega) (by omega) p))
    · exact (cXXip P n hi (by omega) (by omega) (by omega) (Or.inl le_rfl)).mul_right
        (cXEip P n hi (by omega) (by omega) (by omega) (Or.inl (by omega)))
  have hWlv : W ∈ level P n (l-1) := by
    rw [hW]
    exact Subalgebra.mul_mem _ (lv_JP P n hi (by omega) p) (lv_ipX P n hi (by omega))
  -- Term 1
  have T1 : ∀ r', exponentRange k r' →
      W * (JPower P n (g+1) r' * X P n g false * (C * A0)) ∈ Tset P n l i := by
    intro r' hr'
    have e0 : W * (JPower P n (g+1) r' * X P n g false * (C * A0)) =
        JPower P n (g+1) r' * (alphaChain P n i j l p * A0) := by
      rw [hA]; simp only [mul_assoc]; rw [(hWv r').left_comm]
    rw [e0, hA0]
    by_cases hhj : h + 2 ≤ j
    · rw [id1 P n hl hi hig hgh hhj hjl p, ← mul_assoc, JPa]
      have := toT P n (l := l) (i := i) h3 hl (ip := g+1) (jp := h+1) (by omega) (by omega)
        (by omega) (by omega) hr' (Subalgebra.one_mem _)
        (L2_mem1 P n (g := i) (h := j-2) hi (by omega) (by omega) hp)
      simpa only [mul_one] using this
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      rw [id2 P n hl hi hig (by omega) (by omega) (by omega) p, mul_sub, mul_add, mul_smul_comm,
        mul_smul_comm]
      refine sub_mem (add_mem ?_ (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ ?_)
      · rw [← mul_assoc, JPa]
        have := toT P n (l := l) (i := i) h3 hl (ip := g+1) (jp := h+2) (by omega) (by omega)
          (by omega) (by omega) hr' (Subalgebra.one_mem _)
          (L2_mem1 P n (g := i) (h := m) hi (by omega) (by omega) hp)
        simpa only [mul_one] using this
      · rw [← mul_assoc, JPa]
        have := toT P n (l := l) (i := i) h3 hl (ip := g+1) (jp := m+1) (by omega) (by omega)
          (by omega) (by omega) hr' (Subalgebra.one_mem _)
          (L2_mem1 P n (g := i) (h := h) hi (by omega) (by omega) hp)
        simpa only [mul_one] using this
      · rw [← mul_assoc, (cJa P n (by omega) (by omega : g + 1 < m + 2) (by omega) (by omega) hl r' 0).eq]
        exact toT P n (l := l) (i := i) h3 hl (ip := m+2) (jp := h+2) (by omega) (by omega)
          (by omega) (by omega) (pr_zero hk) (lv_JP P n (by omega) (by omega) r')
          (L2_mem1 P n (g := i) (h := g) hi hig (by omega) hp)
  -- Term 2
  have T2 : ∀ s r', exponentRange k s → |r'| ≤ (((k-1)/2 : ℕ) : ℤ) →
      W * (JPower P n (g+1) s * JPower P n g r' * (C * A0)) ∈ Tset P n l i := by
    intro s r' hs hr'
    have hv : alphaChain P n (g+1) j l s = JPower P n (g+1) s * C := by
      rw [hC, ac_def]; simp only [mul_assoc]
    have e : W * (JPower P n (g+1) s * JPower P n g r' * (C * A0)) =
        alphaChain P n (g+1) j l s * W * alphaChain P n g h (l-2) r' := by
      rw [← JPa P n g h (l-2) r', ← hA0, hv]
      simp only [mul_assoc]
      rw [(hWv s).left_comm, (hCu r').left_comm, hWC.left_comm]
    rw [e]
    exact toT P n (l := l) (i := i) h3 hl (ip := g+1) (jp := j) (by omega) (by omega) hjl (by omega)
      hs hWlv (L2_mem1 P n hg hgh hhl (pr_abs hk hr'))
  -- Term 3
  have T3 : ∀ s r', |r'| ≤ (((k-1)/2 : ℕ) : ℤ) →
      W * (JPower P n (g+1) s * E P n g * JPower P n g r' * (C * A0)) ∈ Tset P n l i := by
    intro s r' hr'
    have sh := shiftE P n hg (by omega : g + 1 ≤ j) hjl hl
    have hEC : E P n g * C = intervalProduct (E P n) g (l+1) * Wv P n g (j - (g+1)) := by
      rw [hC, ← mul_assoc]; exact sh.1
    have e : W * (JPower P n (g+1) s * E P n g * JPower P n g r' * (C * A0)) =
        JPower P n i p * intervalProduct (fun t => X P n t false) i g * JPower P n (g+1) s *
          intervalProduct (E P n) g (l+1) * (Wv P n g (j - (g+1)) * alphaChain P n g h (l-2) r') := by
      rw [← JPa P n g h (l-2) r', ← hA0]
      simp only [mul_assoc]
      rw [(hCu r').left_comm, ← mul_assoc (E P n g) C, hEC, hW]
      simp only [mul_assoc]
    rw [e]
    exact T3gen P n hl h3 hi hig (by omega) p s _
      (Lp_Wv P n hl h3 hg (j - (g+1)) (by omega) _
        (as_mem1 P n g h r' hg hgh hhl ⟨le_rfl, hr'⟩))
  -- magic expansion
  have hmain : alphaChain P n i j l p * alphaChain P n g h (l-2) r =
      W * (X P n g false * JPower P n g r * (C * A0)) := by
    rw [hA, ← JPa P n g h (l-2) r, ← hA0]
    simp only [mul_assoc]
    rw [(hCu r).symm.left_comm]
  let F : NonsplitBMW P n →ₗ[R] NonsplitBMW P n :=
    (LinearMap.mulLeft R W).comp (LinearMap.mulRight R (C * A0))
  have hF : ∀ y, F y = W * (y * (C * A0)) := fun _ => rfl
  rw [hmain, ← hF]
  have hgn : g < n := by omega
  have hx1 := x_xi P n g ⟨hg, hgn⟩
  have hx2 := xi_x P n g ⟨hg, hgn⟩
  have hsk := skein P n g ⟨hg, hgn⟩
  have hxe : X P n g false * E P n g = E P n g * X P n g false := by
    rw [xe P n g ⟨hg, hgn⟩, ex P n g ⟨hg, hgn⟩]
  have hv := JM_succ P n false g hg
  have hvi := JM_succ P n true g hg
  unfold exponentRange at hr
  rcases le_or_gt 0 r with hr0 | hr0
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hr0
    have gg := X8B24.g25 (skeinDelta P) _ _ _ _ _ _ _ hx1 hx2 hsk hxe hv hvi q
    rw [← pN, gg, map_add, map_sub, map_smul, map_smul, map_sum, map_sum]
    refine add_mem (sub_mem ?_ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t ht => ?_)))
      (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t ht => ?_))
    · rw [hF, pN]; exact T1 q (by unfold exponentRange; omega)
    · rw [Finset.mem_range] at ht
      rw [hF, pN, pN]
      exact T2 _ _ (by unfold exponentRange; omega) (by rw [abs_le]; omega)
    · rw [Finset.mem_range] at ht
      rw [hF, pN, pN]
      exact T3 _ _ (by rw [abs_le]; omega)
  · obtain ⟨q, hq⟩ : ∃ q : ℕ, r = -(q:ℤ) := ⟨(-r).toNat, by omega⟩
    subst hq
    have gg := X8B24.g26 (skeinDelta P) _ _ _ _ _ _ _ hx1 hx2 hsk hxe hv hvi q
    rw [← pI, gg, map_sub, map_add, map_smul, map_smul, map_sum, map_sum]
    refine sub_mem (add_mem ?_ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t ht => ?_)))
      (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t ht => ?_))
    · rw [hF, pI]; exact T1 _ (by unfold exponentRange; omega)
    · rw [Finset.mem_range] at ht
      rw [hF, pI, pI]
      exact T2 _ _ (by unfold exponentRange; omega) (by rw [abs_le]; omega)
    · rw [Finset.mem_range] at ht
      rw [hF, pI, pI]
      exact T3 _ _ (by rw [abs_le]; omega)

end X8L35

end QAlgorithms.Papers.Independent.Gap48.P01

open QAlgorithms.Papers.Independent.Gap48.P01 in
theorem solution {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)
    (l i j g h : ℕ) (hl : l < n)
    (hi : 1 ≤ i) (hij : i ≤ j) (hjl : j ≤ l)
    (hg : 1 ≤ g) (hgh : g ≤ h) (hhl : h ≤ l-2) (hig : i ≤ g)
    (p r : ℤ) (hp : exponentRange k p) (hr : exponentRange k r) :
    alphaChain P n i j l p * alphaChain P n g h (l-2) r ∈ Submodule.span R
      {z | ∃ ip jp gp hh : ℕ, ∃ pp rr : ℤ,
        1 ≤ ip ∧ ip ≤ jp ∧ jp ≤ l ∧ i < ip ∧
        1 ≤ gp ∧ gp ≤ hh ∧ hh ≤ l-2 ∧ exponentRange k pp ∧ exponentRange k rr ∧
        ∃ b ∈ level P n (l-3),
          z = alphaChain P n ip jp l pp * alphaChain P n gp hh (l-2) rr * b} :=
  X8L35.main35 P n l i j g h hl hi hij hjl hg hgh hhl hig p r hp hr

-- Prove2me | solution 1 for SphereSOS.DPS.eq_37
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T01:53:05.431999+00:00
-- url     : https://prove2.me/submissions/43cc607e-56a1-49ce-8622-683007491e0d

import Definitions.Def_SphereSOS_DPS_Setting
import Mathlib.Tactic.LinearCombination

open SphereSOS.DPS Matrix
open scoped BigOperators

namespace SphereEq37Proof

def pairSwap {dA dB ℓ : ℕ} (s : ℕ) :
    (Fin dA × (Fin ℓ → Fin dB)) × (Fin dA × (Fin ℓ → Fin dB)) ≃
      (Fin dA × (Fin ℓ → Fin dB)) × (Fin dA × (Fin ℓ → Fin dB)) where
  toFun pq := ((pq.1.1, fun i => if (i : ℕ) < s then pq.2.2 i else pq.1.2 i),
    (pq.2.1, fun i => if (i : ℕ) < s then pq.1.2 i else pq.2.2 i))
  invFun pq := ((pq.1.1, fun i => if (i : ℕ) < s then pq.2.2 i else pq.1.2 i),
    (pq.2.1, fun i => if (i : ℕ) < s then pq.1.2 i else pq.2.2 i))
  left_inv pq := by ext <;> simp only <;> split <;> simp_all
  right_inv pq := by ext <;> simp only <;> split <;> simp_all

lemma coeff_swap {dA dB ℓ : ℕ} (s : ℕ) (x : Fin dA → ℂ) (y : Fin dB → ℂ)
    (pq : (Fin dA × (Fin ℓ → Fin dB)) × (Fin dA × (Fin ℓ → Fin dB))) :
    star (tensVec s x y pq.1) * tensVec s x y pq.2 =
      star (tensVec 0 x y ((pairSwap s pq).1)) * tensVec 0 x y ((pairSwap s pq).2) := by
  simp only [tensVec, star_mul, star_prod, pairSwap, Equiv.coe_fn_mk, Nat.not_lt_zero,
    ↓reduceIte, star_star]
  have hprod : (∏ i : Fin ℓ, star (if (i : ℕ) < s then star (y (pq.1.2 i)) else y (pq.1.2 i))) *
      (∏ i : Fin ℓ, if (i : ℕ) < s then star (y (pq.2.2 i)) else y (pq.2.2 i)) =
      (∏ i : Fin ℓ, star (y (if (i : ℕ) < s then pq.2.2 i else pq.1.2 i))) *
      (∏ i : Fin ℓ, y (if (i : ℕ) < s then pq.1.2 i else pq.2.2 i)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    split <;> simp_all [mul_comm]
  linear_combination (star (x pq.1.1) * x pq.2.1) * hprod

end SphereEq37Proof

open SphereEq37Proof

theorem solution {dA dB m : ℕ} (s : ℕ) (hs : s ≤ m + 1)
    (W : Matrix (Fin dA × (Fin (m + 1) → Fin dB)) (Fin dA × (Fin (m + 1) → Fin dB)) ℂ)
    (x : Fin dA → ℂ) (y : Fin dB → ℂ) :
    qf (tensVec s x y) W = qf (tensVec 0 x y) (ptB s W) := by
  classical
  simp only [qf, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  apply Fintype.sum_equiv (pairSwap s)
  intro pq
  have h := coeff_swap s x y pq
  calc
    star (tensVec s x y pq.1) * (W pq.1 pq.2 * tensVec s x y pq.2) =
        (star (tensVec s x y pq.1) * tensVec s x y pq.2) * W pq.1 pq.2 := by ring
    _ = (star (tensVec 0 x y ((pairSwap s pq).1)) * tensVec 0 x y ((pairSwap s pq).2)) * W pq.1 pq.2 := by rw [h]
    _ = _ := by
      have hpt : ptB s W ((pairSwap s pq).1) ((pairSwap s pq).2) = W pq.1 pq.2 := by
        simp only [ptB, pairSwap, Equiv.coe_fn_mk]
        congr 2 <;> ext i <;> split <;> simp_all
      rw [hpt]
      ring


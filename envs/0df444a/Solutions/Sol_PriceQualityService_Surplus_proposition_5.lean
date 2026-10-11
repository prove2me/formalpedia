-- Prove2me | solution 1 for PriceQualityService.Surplus.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:18:39.227431+00:00
-- url     : https://prove2.me/submissions/aad56873-7c40-471e-9681-6a6a7c547022

import Mathlib
import Definitions.Def_PriceQualityService_Surplus_Problems
import Definitions.Def_PriceQualityService_Surplus_ConsumerSurplus

namespace RRAux_PriceQualityService_Surplus_proposition_5

open PriceQualityService.Joint

theorem term_le (y u : ℝ) : y * Real.exp u ≤ Real.exp (u + y - 1) := by
  rw [show u + y - 1 = (y - 1) + u by ring, Real.exp_add]
  have := Real.add_one_le_exp (y - 1)
  have hu := Real.exp_pos u
  nlinarith

theorem term_eq (y u : ℝ) (h : y * Real.exp u = Real.exp (u + y - 1)) : y = 1 := by
  by_contra hy
  have := Real.add_one_lt_exp (show y - 1 ≠ 0 from sub_ne_zero.mpr hy)
  rw [show u + y - 1 = (y - 1) + u by ring, Real.exp_add] at h
  have hu := Real.exp_pos u
  nlinarith

theorem one_add_sum_pos {N : ℕ} (α s p q t : Fin N → ℝ) :
    0 < 1 + ∑ j, attraction α s p q t j := by
  have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (Real.exp_pos
    (α j * q j - p j + t j * s j)).le)
  unfold attraction
  linarith

theorem prof_mul {N : ℕ} (α a b c s p q t : Fin N → ℝ) :
    profit α a b c s p q t * (1 + ∑ j, attraction α s p q t j) =
      ∑ i, markup a b c p q t i * attraction α s p q t i := by
  have hpos := one_add_sum_pos α s p q t
  unfold profit choiceProb
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

theorem key {N : ℕ} (α a b c s q t p : Fin N → ℝ)
    (hopt : ∀ p' : Fin N → ℝ, profit α a b c s p' q t ≤ profit α a b c s p q t) :
    ∑ i, attraction α s p q t i = profit α a b c s p q t := by
  obtain ⟨r, hr⟩ : ∃ r, profit α a b c s p q t = r := ⟨_, rfl⟩
  rw [hr] at hopt ⊢
  have hX := prof_mul α a b c s p q t
  rw [hr] at hX
  let p' : Fin N → ℝ := fun i => c i * q i ^ 2 + t i * (a i - b i * q i) + r + 1
  have hm' : ∀ i, markup a b c p' q t i = r + 1 := by
    intro i; simp only [markup, p']; ring
  have hE := prof_mul α a b c s p' q t
  have hEpos := one_add_sum_pos α s p' q t
  have hle := mul_le_mul_of_nonneg_right (hopt p') hEpos.le
  rw [hE] at hle
  simp only [hm'] at hle
  rw [← Finset.mul_sum] at hle
  -- hle : (r+1) * E ≤ r * (1 + E)
  have hEr : ∑ j, attraction α s p' q t j ≤ r := by nlinarith
  have hatt : ∀ i, attraction α s p' q t i =
      Real.exp ((α i * q i - p i + t i * s i) + (markup a b c p q t i - r) - 1) := by
    intro i; unfold attraction; congr 1; simp only [markup, p']; ring
  have hterm : ∀ i, (markup a b c p q t i - r) * attraction α s p q t i ≤
      attraction α s p' q t i := by
    intro i; rw [hatt i]; exact term_le _ _
  have hsum : ∑ i, (markup a b c p q t i - r) * attraction α s p q t i = r := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    linarith
  have hEeq : ∑ j, attraction α s p' q t j = r := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
    linarith
  have hzero : ∑ i, (attraction α s p' q t i -
      (markup a b c p q t i - r) * attraction α s p q t i) = 0 := by
    rw [Finset.sum_sub_distrib]; linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.mpr (hterm i))] at hzero
  have hxi : ∀ i, attraction α s p q t i = attraction α s p' q t i := by
    intro i
    have h0 := hzero i (Finset.mem_univ _)
    have heq : (markup a b c p q t i - r) * attraction α s p q t i = attraction α s p' q t i := by
      linarith
    have hy : markup a b c p q t i - r = 1 := by
      rw [hatt i] at heq
      exact term_eq _ _ (by simpa [attraction] using heq)
    rw [hy, one_mul] at heq
    exact heq
  rw [Finset.sum_congr rfl (fun i _ => hxi i), hEeq]

end RRAux_PriceQualityService_Surplus_proposition_5

open PriceQualityService.Surplus in
open Finset in
-- Proposition 5, Wang, Ke & Cui
theorem solution {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ)
    (hc : ∀ i, 0 < c i) (hts : ts ≤ tl)
    (q t : Fin N → ℝ) (ht : ∀ i, t i ∈ Set.Icc ts tl)
    (pDag : Fin N → ℝ) (hDag : IsPriceOptimal α a b c s q t pDag)
    (pDdag tDdag : Fin N → ℝ) (hDdag : IsPriceServiceOptimal α a b c s ts tl q pDdag tDdag)
    (pStar qStar tStar : Fin N → ℝ) (hStar : IsJointOptimal α a b c s ts tl pStar qStar tStar) :
    consumerSurplus α s pDag q t ≤ consumerSurplus α s pDdag q tDdag ∧
      consumerSurplus α s pDdag q tDdag ≤ consumerSurplus α s pStar qStar tStar := by
  open RRAux_PriceQualityService_Surplus_proposition_5 in
  have k1 := key α a b c s q t pDag hDag
  have k2 := key α a b c s q tDdag pDdag (fun p' => hDdag.2 p' tDdag hDdag.1)
  have k3 := key α a b c s qStar tStar pStar (fun p' => hStar.2 p' qStar tStar hStar.1)
  have l1 := hDdag.2 pDag t ht
  have l2 := hStar.2 pDdag q tDdag hDdag.1
  have pos1 := one_add_sum_pos α s pDag q t
  have pos2 := one_add_sum_pos α s pDdag q tDdag
  unfold consumerSurplus
  rw [k1, k2, k3] at *
  rw [k1] at pos1; rw [k2] at pos2
  exact ⟨Real.log_le_log pos1 (by linarith), Real.log_le_log pos2 (by linarith)⟩

#print axioms solution

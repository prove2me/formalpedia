-- Prove2me | solution 1 for PriceQualityService.Dealer.eq_EC_11
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:42:32.149887+00:00
-- url     : https://prove2.me/submissions/4792f7ef-a4d5-40ca-9a91-0bc0faaed195

import Mathlib
import Definitions.Def_PriceQualityService_Dealer_Model
import Definitions.Def_PriceQualityService_Dealer_Breakpoints

set_option autoImplicit false
open Finset PriceQualityService.Dealer

theorem solution {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ)
    (Sl Ss : Finset (Fin N)) (hdisj : Disjoint Sl Ss) (r : ℝ) :
    r = dealerProfit α a b c s p q ts tl Sl Ss ↔
      r = ∑ i ∈ Sl, hLong α a b c s p q tl i r + ∑ i ∈ Ss, hShort α a b c s p q ts i r := by
  set A := ∑ j ∈ Sl, attraction α s p q tl j + ∑ j ∈ Ss, attraction α s p q ts j with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact add_nonneg (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le)
      (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le)
  have hD : choiceDenom α s p q ts tl Sl Ss = 1 + A := by
    unfold choiceDenom; rw [hA]; ring
  have hDpos : 0 < 1 + A := by linarith
  set M := ∑ i ∈ Sl, markup a b c p q tl i * attraction α s p q tl i +
      ∑ i ∈ Ss, markup a b c p q ts i * attraction α s p q ts i with hM
  have hprofit : dealerProfit α a b c s p q ts tl Sl Ss = M / (1 + A) := by
    unfold dealerProfit
    have h1 : ∑ i ∈ Sl, markup a b c p q tl i * choiceProb α s p q ts tl Sl Ss i =
        (∑ i ∈ Sl, markup a b c p q tl i * attraction α s p q tl i) / (1 + A) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      unfold choiceProb
      rw [if_pos hi, hD]; ring
    have h2 : ∑ i ∈ Ss, markup a b c p q ts i * choiceProb α s p q ts tl Sl Ss i =
        (∑ i ∈ Ss, markup a b c p q ts i * attraction α s p q ts i) / (1 + A) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ∉ Sl := Finset.disjoint_right.mp hdisj hi
      unfold choiceProb
      rw [if_neg hi', if_pos hi, hD]; ring
    rw [h1, h2, hM]; ring
  have hrhs : ∑ i ∈ Sl, hLong α a b c s p q tl i r + ∑ i ∈ Ss, hShort α a b c s p q ts i r =
      M - r * A := by
    unfold hLong hShort
    rw [hM, hA]
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hprofit, hrhs]
  constructor
  · intro h
    rw [h]; field_simp; ring
  · intro h
    rw [eq_div_iff hDpos.ne']
    linarith

-- Prove2me | solution 1 for RhinViola.normalizedLogLimitToExponentialBounds
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:42:47.016014+00:00
-- url     : https://prove2.me/submissions/69363845-a140-43bd-b16a-12e75df5938c

import Theorems.Thm_RhinViola_normalizedLogLimitEventuallyBand
import Theorems.Thm_RhinViola_normalizedLogBoundsToExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false

theorem solution
    (sigma : Real) (f : Nat -> Real)
    (hlim : Filter.Tendsto (fun n : Nat => Real.log |f n| / (n : Real)) Filter.atTop (nhds (-sigma)))
    (hnz : exists N0 : Nat, forall n : Nat, N0 <= n -> f n != 0) :
    forall delta : Real, 0 < delta ->
      exists N : Nat, forall n : Nat, N <= n ->
        Real.exp (-((sigma + delta) * (n : Real))) <= |f n| /\
        |f n| <= Real.exp (-((sigma - delta) * (n : Real))) := by
  intro delta hdelta
  obtain ⟨N0, hN0⟩ := hnz
  obtain ⟨N, hN⟩ := RhinViola.normalizedLogLimitEventuallyBand sigma delta
    (fun n : Nat => Real.log |f n| / (n : Real)) hdelta hlim
  refine ⟨max (max N N0) 1, fun n hn => ?_⟩
  have hNn : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hN0n : N0 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hpos : 0 < n := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _) hn)
  have hf : f n ≠ 0 := bne_iff_ne.mp (hN0 n hN0n)
  exact RhinViola.normalizedLogBoundsToExponentialBounds sigma delta (f n) n hpos hf
    (hN n hNn).1 (hN n hNn).2

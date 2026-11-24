-- Prove2me | solution 1 for RhinViola.normalizedLogCoefficientLimitToExponentialBound
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:41:53.318345+00:00
-- url     : https://prove2.me/submissions/22c55e15-48b8-4ae6-92a1-0c5865c4a6c4

import Theorems.Thm_RhinViola_normalizedLogLimitEventuallyBand
import Theorems.Thm_RhinViola_normalizedLogCoefficientBoundToExponential
import Mathlib.Tactic

set_option autoImplicit false

theorem solution
    (rho : Real) (b : Nat -> Int)
    (hlim : Filter.Tendsto (fun n : Nat => Real.log |(b n : Real)| / (n : Real)) Filter.atTop (nhds rho)) :
    forall delta : Real, 0 < delta ->
      exists N : Nat, forall n : Nat, N <= n ->
        |(b n : Real)| <= Real.exp ((rho + delta) * (n : Real)) := by
  intro delta hdelta
  have hlim' : Filter.Tendsto (fun n : Nat => Real.log |(b n : Real)| / (n : Real))
      Filter.atTop (nhds (-(-rho))) := by simpa using hlim
  obtain ⟨N, hN⟩ := RhinViola.normalizedLogLimitEventuallyBand (-rho) delta
    (fun n : Nat => Real.log |(b n : Real)| / (n : Real)) hdelta hlim'
  refine ⟨max N 1, fun n hn => ?_⟩
  have hNn : N ≤ n := le_trans (le_max_left _ _) hn
  have hpos : 0 < n := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _) hn)
  have hup := (hN n hNn).2
  apply RhinViola.normalizedLogCoefficientBoundToExponential rho delta (b n) n hpos
  have : -(-rho - delta) = rho + delta := by ring
  simpa [this] using hup

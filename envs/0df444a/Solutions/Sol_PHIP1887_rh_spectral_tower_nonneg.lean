-- Prove2me | solution 1 for PHIP1887.rh_spectral_tower_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:09:58.060918+00:00
-- url     : https://prove2.me/submissions/54acd466-4236-4c20-bfb7-30c5c3859a4e

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
import Theorems.Thm_PHIP1887_positive_spectrum_tower
import Theorems.Thm_PHIP1887_critical_coordinate
import Theorems.Thm_PHIP1887_critical_zero_coordinate
open MeasureTheory Set
open PHIP1887

theorem solution (rho : ℕ → ℂ) (x : ℝ) (p q : ℕ)
    (hRH : RiemannHypothesis)
    (hzero : ∀ j, riemannZeta (rho j) = 0)
    (htrivial : ∀ j, ¬ ∃ n : ℕ, rho j = -2*((n:ℂ)+1))
    (hone : ∀ j, rho j ≠ 1)
    (him : ∀ j, (rho j).im ≠ 0)
    (hx : 0 < x)
    (hs : Summable (fun j =>
      (atom (zeroCoordinate x (rho j)) p q).re)) :
    0 ≤ spectralTower rho x p q := by
  have hr : ∀ j, (rho j).re = 1/2 :=
    fun j => hRH (rho j) (hzero j) (htrivial j) (hone j)
  have heq : (fun j => zeroCoordinate x (rho j)) =
      (fun j => ((x/(x+(rho j).im^2) : ℝ) : ℂ)) := by
    funext j
    exact critical_zero_coordinate (rho j) x (hr j)
  unfold spectralTower
  rw [heq]
  apply positive_spectrum_tower
  · intro j
    have hh := critical_coordinate x ((rho j).im^2) hx (sq_pos_of_ne_zero (him j))
    exact ⟨le_of_lt hh.1, le_of_lt hh.2⟩
  · have hh : (fun j => (atom (zeroCoordinate x (rho j)) p q).re) =
        (fun j => (atom ((x/(x+(rho j).im^2) : ℝ) : ℂ) p q).re) := by
      funext j
      rw [critical_zero_coordinate (rho j) x (hr j)]
    rw [hh] at hs
    exact hs

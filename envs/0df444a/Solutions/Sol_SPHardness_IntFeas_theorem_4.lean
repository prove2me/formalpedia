-- Prove2me | solution 1 for SPHardness.IntFeas.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T08:59:10.428485+00:00
-- url     : https://prove2.me/submissions/a99cfaca-beee-40bf-961c-98525c5b9ab9

import Mathlib
import Definitions.Def_SPHardness_IntFeas_Model
import Theorems.Thm_SPHardness_IntFeas_xStar_dichotomy
import Theorems.Thm_SPHardness_IntFeas_epsOptimal_bound

open MeasureTheory
open SPHardness.IntFeas

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hinst : IsIFPInstance A b) (hne : ∃ ξ : Fin n → ℝ, InPolytope A b ξ) (hn : 1 ≤ n)
    (ε' : ℝ) (hε'0 : 0 ≤ ε') (hε'half : ε' < 1 / 2)
    (hε'row : ∀ i, ε' * ∑ j, |(A i j : ℝ)| < 1)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < ε' / (4 * n))
    (x : ℝ) (hx : IsEpsOptimal A b ε x) :
    IFPAnswer A b ↔ (n : ℝ) - ε' / 2 < x := by
  have hb := epsOptimal_bound A b hinst hne hn ε hε0 x hx
  obtain ⟨h1, h2⟩ := xStar_dichotomy A b hinst hne ε' hε'0 hε'half hε'row
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h4 : 2 * (n : ℝ) * ε < ε' / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hε
    nlinarith
  have hab := abs_le.mp hb
  constructor
  · intro h
    have := h1.mp h
    linarith [hab.1, hab.2]
  · intro h
    by_contra hc
    have := h2.mp hc
    linarith [hab.1, hab.2]

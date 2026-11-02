-- Prove2me | solution 1 for QuantumMaxCutEnergy.scalar_full_0595
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T04:50:23.840375+00:00
-- url     : https://prove2.me/submissions/3dd228a7-9962-4e02-8630-b7fb94f6b713

import Mathlib

open scoped BigOperators

noncomputable section

namespace QuantumMaxCutEnergy

/-! ### 2. The scalar inequality of the mixing step on the full domain

The moment relaxation only constrains `s_e = -(L(XXₑ)+L(YYₑ)+L(ZZₑ))/3` to
`[-1/3, 1]`, while the platform's `lp24_strict_scalar` covers `s ∈ [0,1]`.
Below, the negative half `s ∈ [-1/3, 0]` is proved outright: there the
matching (positive-excess) term vanishes and the crude bound
`(1 + 0.8488 s + 0.08488 s³)/2 ≥ 1/2 - 0.14305` suffices. -/

/-- The product/GP term of the scalar. -/
def prodTerm (s : ℝ) : ℝ := (1 + 0.8488 * s + 0.08488 * s ^ 3) / 2

/-- The matching term of the scalar, with the paper's `4/5` factor. -/
def matchTerm (s : ℝ) : ℝ := 1 / 2 + (3 / 2) * (4 / 5) * max ((3 * s - 1) / 2) 0

/-- The mixture bound of the scalar. -/
def mixTerm (p s : ℝ) : ℝ := p * prodTerm s + (1 - p) * matchTerm s

theorem prodTerm_lower (s : ℝ) (h : -1 / 3 ≤ s) (h' : s ≤ 0) :
    (1 / 2 - 0.14305 : ℝ) ≤ prodTerm s := by
  have h2 : s ^ 2 ≤ 1 / 9 := by nlinarith
  have h3 : (0 : ℝ) ≤ s ^ 2 + 1 / 9 := by positivity
  have h4 : s ^ 3 ≥ -1 / 27 := by
    have : s ^ 3 = s * s ^ 2 := by ring
    rw [this]
    nlinarith
  have h5 : 0.8488 * s ≥ -0.8488 / 3 := by nlinarith
  have h6 : 0.08488 * s ^ 3 ≥ -0.08488 / 27 := by nlinarith
  unfold prodTerm
  nlinarith

/-- **The scalar on the negative half.** -/
theorem scalar_nonpos (s : ℝ) (h : -1 / 3 ≤ s) (h' : s ≤ 0) :
    (0.5955 : ℝ) * ((1 + 3 * s) / 2) ≤ mixTerm 0.672 s := by
  have hprod := prodTerm_lower s h h'
  have hmax : (0 : ℝ) ≤ max ((3 * s - 1) / 2) 0 := le_max_right _ _
  have hc : (1 + 3 * s) / 2 ≤ 1 / 2 := by linarith
  have hc0 : (0 : ℝ) ≤ (1 + 3 * s) / 2 := by linarith
  unfold mixTerm matchTerm prodTerm at *
  nlinarith

/-- **The scalar inequality on the whole admissible range `s ∈ [-1/3, 1]`**,
from its positive half (the platform's `lp24_strict_scalar`). -/
theorem scalar_full (hpos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (0.5955 : ℝ) * ((1 + 3 * s) / 2) ≤ mixTerm 0.672 s)
    (s : ℝ) (h : -1 / 3 ≤ s) (h' : s ≤ 1) :
    (0.5955 : ℝ) * ((1 + 3 * s) / 2) ≤ mixTerm 0.672 s := by
  by_cases hs : 0 ≤ s
  · exact hpos s hs h'
  · exact scalar_nonpos s h (not_le.mp hs).le

end QuantumMaxCutEnergy

/-- LP24's mixing inequality on the full admissible range, packaged as the platform solution. -/
theorem solution (hpos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (0.5955 : ℝ) * ((1 + 3 * s) / 2) ≤
        0.672 * ((1 + 0.8488 * s + 0.08488 * s ^ 3) / 2) +
          (1 - 0.672) * (1 / 2 + (3 / 2) * (4 / 5) * max ((3 * s - 1) / 2) 0))
    (s : ℝ) (h : -1 / 3 ≤ s) (h' : s ≤ 1) :
    (0.5955 : ℝ) * ((1 + 3 * s) / 2) ≤
      0.672 * ((1 + 0.8488 * s + 0.08488 * s ^ 3) / 2) +
        (1 - 0.672) * (1 / 2 + (3 / 2) * (4 / 5) * max ((3 * s - 1) / 2) 0) :=
  QuantumMaxCutEnergy.scalar_full hpos s h h'

#print axioms solution

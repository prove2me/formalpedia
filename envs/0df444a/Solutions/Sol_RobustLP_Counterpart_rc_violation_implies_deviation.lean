-- Prove2me | solution 1 for RobustLP.Counterpart.rc_violation_implies_deviation
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:25:21.002034+00:00
-- url     : https://prove2.me/submissions/57e00667-fd5f-4327-8811-bc23a95856b3

import Mathlib
import Definitions.Def_RobustLP_Counterpart_UncertainLP
import Definitions.Def_RobustLP_Counterpart_RobustCounterparts
open scoped BigOperators

namespace RobustLP.Counterpart

/-- **Proof of Proposition 1, displayed chain** (Ben-Tal–Nemirovski 2000, §3.1, p. 419), in
corrected pointwise form. Let `ε > 0`, `δ > 0`, `Ω > 0` and let `(x, y, z)` be feasible for
(RC[ε, δ, Ω]). Fix a row `i` and a realization `ξi` of the perturbations of that row, with
`ξi j = 0` for `j ∉ J i` and `|ξi j| ≤ 1`. If the perturbed constraint
`∑_j (1 + ε ξi_j) a_{ij} x_j > b_i + δ max[1, |b_i|]` is violated, then
`∑_{j ∈ J_i} ξi_j a_{ij} z_{ij} > Ω √(∑_{j ∈ J_i} a_{ij}² z_{ij}²)`. -/
theorem _root_.solution {n p m : ℕ} (L : UncertainLP n p m)
    (ε δ Ω : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hΩ : 0 < Ω)
    (x : Fin n → ℝ) (y z : Fin m → Fin n → ℝ) (hRC : L.RCFeasible ε δ Ω x y z)
    (i : Fin m) (ξi : Fin n → ℝ) (hξ0 : ∀ j ∉ L.J i, ξi j = 0) (hξ1 : ∀ j, |ξi j| ≤ 1)
    (hviol : L.bPlus δ i < ∑ j, (1 + ε * ξi j) * L.A i j * x j) :
    Ω * Real.sqrt (∑ j ∈ L.J i, L.A i j ^ 2 * z i j ^ 2) <
      ∑ j ∈ L.J i, ξi j * L.A i j * z i j := by
  classical
  rcases hRC with ⟨hE, hA, hb, hbox, hyz⟩
  have hpt (j : Fin n) (hj : j ∈ L.J i) :
      ξi j * L.A i j * x j ≤ |L.A i j| * y i j + ξi j * L.A i j * z i j := by
    have habs : |x j - z i j| ≤ y i j := abs_le.mpr (hyz i j)
    have h1 := mul_le_mul_of_nonneg_right (hξ1 j) (abs_nonneg (L.A i j))
    have h2 := mul_le_mul_of_nonneg_right h1 (abs_nonneg (x j - z i j))
    have h3 := mul_le_mul_of_nonneg_left habs (abs_nonneg (L.A i j))
    have h4 := le_abs_self (ξi j * L.A i j * (x j - z i j))
    simp only [abs_mul] at h4
    nlinarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib] at hsum
  have hsupport : (∑ j, ξi j * L.A i j * x j) = ∑ j ∈ L.J i, ξi j * L.A i j * x j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j hj hj'
    simp [hξ0 j hj']
  have hexpand : (∑ j, (1 + ε * ξi j) * L.A i j * x j) =
      (∑ j, L.A i j * x j) + ε * ∑ j ∈ L.J i, ξi j * L.A i j * x j := by
    rw [← hsupport, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hexpand] at hviol
  have hscaled := mul_le_mul_of_nonneg_left hsum hε.le
  have hi := hb i
  nlinarith


end RobustLP.Counterpart

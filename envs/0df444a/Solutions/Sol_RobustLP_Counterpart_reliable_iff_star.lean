-- Prove2me | solution 1 for RobustLP.Counterpart.reliable_iff_star
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:26:42.936745+00:00
-- url     : https://prove2.me/submissions/43437205-3ccf-4cae-990f-b855ca3b4986

import Mathlib
import Definitions.Def_RobustLP_Counterpart_UncertainLP
import Definitions.Def_RobustLP_Counterpart_Reliable
import Definitions.Def_RobustLP_Counterpart_RobustCounterparts
open scoped BigOperators

namespace RobustLP.Counterpart

/-- **Reliability ⇔ (∗)** (Ben-Tal–Nemirovski 2000, §3.1, p. 417). For `ε > 0` and `δ > 0`,
`x` is reliable (conditions (i) and (ii)) if and only if `x` is a feasible solution of (∗). -/
theorem _root_.solution {n p m : ℕ} (L : UncertainLP n p m)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (x : Fin n → ℝ) :
    L.Reliable ε δ x ↔ L.StarFeasible ε δ x := by
  classical
  constructor
  · rintro ⟨hLP, hpert⟩
    refine ⟨hLP.1, hLP.2.1, ?_, hLP.2.2⟩
    intro i
    let a : Fin n → ℝ := fun j => if 0 ≤ x j then L.A i j + ε * |L.A i j| else L.A i j - ε * |L.A i j|
    have ha (j : Fin n) (hj : j ∈ L.J i) : |a j - L.A i j| ≤ ε * |L.A i j| := by
      dsimp [a]
      split_ifs <;> simp [abs_of_nonneg (mul_nonneg hε.le (abs_nonneg (L.A i j)))]
    have hprod (j : Fin n) : a j * x j = L.A i j * x j + ε * |L.A i j| * |x j| := by
      dsimp [a]
      split_ifs with hx
      · rw [abs_of_nonneg hx]; ring
      · rw [abs_of_neg (lt_of_not_ge hx)]; ring
    have hh := hpert i a ha
    simp_rw [hprod] at hh
    rw [Finset.sum_add_distrib, ← add_assoc, Finset.sum_compl_add_sum] at hh
    simpa only [Finset.mul_sum, mul_assoc] using hh
  · rintro ⟨hE, hA, hstar, hbox⟩
    refine ⟨⟨hE, hA, hbox⟩, ?_⟩
    intro i a ha
    have hprod (j : Fin n) (hj : j ∈ L.J i) :
        a j * x j ≤ L.A i j * x j + ε * |L.A i j| * |x j| := by
      have hh := mul_le_mul_of_nonneg_right (ha j hj) (abs_nonneg (x j))
      have habs := le_abs_self ((a j - L.A i j) * x j)
      rw [abs_mul] at habs
      nlinarith
    have hsum := Finset.sum_le_sum hprod
    rw [Finset.sum_add_distrib] at hsum
    have hsplit := Finset.sum_compl_add_sum (L.J i) (fun j => L.A i j * x j)
    have hstar' := hstar i
    simp only [Finset.mul_sum, mul_assoc] at hstar'
    simp only [mul_assoc] at hsum
    linarith


end RobustLP.Counterpart

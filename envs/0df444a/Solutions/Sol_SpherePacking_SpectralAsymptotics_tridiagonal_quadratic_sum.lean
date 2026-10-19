-- Prove2me | solution 1 for SpherePacking.SpectralAsymptotics.tridiagonal_quadratic_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/a1ef6fd8-f81e-4e96-b0cb-45b67d3db4f1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open SpherePacking
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology InnerProductSpace
open SpherePacking.SpectralAsymptotics
open SpherePacking.NumericalCertificate
namespace SpherePacking.SpectralAsymptotics
theorem _root_.solution
    (d : ℕ) (c v : ℕ → ℝ) :
    (∑ p ∈ Finset.range (d + 1),
      ∑ q ∈ Finset.range (d + 1),
        (if p + 1 = q then c p
          else if q + 1 = p then c q else 0) * v q * v p) =
      2 * ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by
  have hpoint (p q : ℕ) :
      (if p + 1 = q then c p
        else if q + 1 = p then c q else 0) * v q * v p =
        (if p + 1 = q then c p * v q * v p else 0) +
        (if q + 1 = p then c q * v q * v p else 0) := by
    by_cases h₁ : p + 1 = q
    · have h₂ : ¬ q + 1 = p := by omega
      simp [h₁, h₂]
    · by_cases h₂ : q + 1 = p
      · simp [h₁, h₂]
      · simp [h₁, h₂]
  have hupper :
      (∑ p ∈ Finset.range (d + 1),
        ∑ q ∈ Finset.range (d + 1),
          if p + 1 = q then c p * v q * v p else 0) =
        ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by
    simp only [Finset.sum_ite_eq, Finset.mem_range]
    rw [Finset.sum_range_succ]
    simp only [lt_self_iff_false, ite_false, add_zero]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : p < d := Finset.mem_range.mp hp
    simp [hp', mul_comm, mul_left_comm, mul_assoc]
  have hlower :
      (∑ p ∈ Finset.range (d + 1),
        ∑ q ∈ Finset.range (d + 1),
          if q + 1 = p then c q * v q * v p else 0) =
        ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by
    rw [Finset.sum_comm]
    calc
      (∑ q ∈ Finset.range (d + 1),
        ∑ p ∈ Finset.range (d + 1),
          if q + 1 = p then c q * v q * v p else 0) =
        ∑ q ∈ Finset.range (d + 1),
          ∑ p ∈ Finset.range (d + 1),
            if q + 1 = p then c q * v p * v q else 0 := by
              apply Finset.sum_congr rfl
              intro q hq
              apply Finset.sum_congr rfl
              intro p hp
              split_ifs <;> ring
      _ = _ := hupper
  calc
    (∑ p ∈ Finset.range (d + 1),
      ∑ q ∈ Finset.range (d + 1),
        (if p + 1 = q then c p
          else if q + 1 = p then c q else 0) * v q * v p) =
        ∑ p ∈ Finset.range (d + 1),
          ∑ q ∈ Finset.range (d + 1),
            ((if p + 1 = q then c p * v q * v p else 0) +
             (if q + 1 = p then c q * v q * v p else 0)) := by
              apply Finset.sum_congr rfl
              intro p hp
              apply Finset.sum_congr rfl
              intro q hq
              exact hpoint p q
    _ =
        (∑ p ∈ Finset.range (d + 1),
          ∑ q ∈ Finset.range (d + 1),
            if p + 1 = q then c p * v q * v p else 0) +
        (∑ p ∈ Finset.range (d + 1),
          ∑ q ∈ Finset.range (d + 1),
            if q + 1 = p then c q * v q * v p else 0) := by
              simp_rw [Finset.sum_add_distrib]
    _ = 2 * ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by
      rw [hupper, hlower]
      ring
end SpherePacking.SpectralAsymptotics

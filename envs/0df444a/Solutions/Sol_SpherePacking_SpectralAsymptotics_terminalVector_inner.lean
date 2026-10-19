-- Prove2me | solution 1 for SpherePacking.SpectralAsymptotics.terminalVector_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/b5b6fcc2-88ed-4e1c-8d25-ee0ddc99c29f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tridiagonal_quadratic_sum
import Theorems.Thm_MetricCodes_Hamming_terminal_indicator_edge_sum
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_tridiagonal_quadratic_sum
import Theorems.Thm_SpherePacking_SpectralAsymptotics_tridiagonal_quadratic_sum
import Theorems.Thm_SpherePacking_SpectralAsymptotics_terminal_indicator_edge_sum

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
    (n k L m : ℕ) (hkl : k ≤ L) (hm : m ≤ L - k) :
    @inner ℝ (Jacobi.Space k L) _
        (Jacobi.operator n k L (terminalVector k L m))
        (terminalVector k L m) =
      2 * ∑ r ∈ Finset.range m,
        Gegenbauer.jacobiCoefficient n k (L - m + r) := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ p : Fin (L - k + 1),
      (∑ q : Fin (L - k + 1),
        (if p.val + 1 = q.val then
          Gegenbauer.jacobiCoefficient n k (k + p.val)
        else if q.val + 1 = p.val then
          Gegenbauer.jacobiCoefficient n k (k + q.val)
        else 0) * terminalIndicator (L - k) m q.val) *
        terminalIndicator (L - k) m p.val) =
      2 * ∑ r ∈ Finset.range m,
        Gegenbauer.jacobiCoefficient n k (L - m + r)
  simp_rw [Finset.sum_mul]
  let f : ℕ → ℝ := fun p =>
    ∑ q : Fin (L - k + 1),
      (if p + 1 = q.val then
        Gegenbauer.jacobiCoefficient n k (k + p)
      else if q.val + 1 = p then
        Gegenbauer.jacobiCoefficient n k (k + q.val)
      else 0) * terminalIndicator (L - k) m q.val *
        terminalIndicator (L - k) m p
  change
    (∑ p : Fin (L - k + 1), f p.val) =
      2 * ∑ r ∈ Finset.range m,
        Gegenbauer.jacobiCoefficient n k (L - m + r)
  rw [Fin.sum_univ_eq_sum_range f]
  dsimp only [f]
  have hfin (p : ℕ) :
      (∑ q : Fin (L - k + 1),
        (if p + 1 = q.val then
          Gegenbauer.jacobiCoefficient n k (k + p)
        else if q.val + 1 = p then
          Gegenbauer.jacobiCoefficient n k (k + q.val)
        else 0) * terminalIndicator (L - k) m q.val *
          terminalIndicator (L - k) m p) =
        ∑ q ∈ Finset.range (L - k + 1),
          (if p + 1 = q then
            Gegenbauer.jacobiCoefficient n k (k + p)
          else if q + 1 = p then
            Gegenbauer.jacobiCoefficient n k (k + q)
          else 0) * terminalIndicator (L - k) m q *
            terminalIndicator (L - k) m p := by
    let g : ℕ → ℝ := fun q =>
      (if p + 1 = q then
        Gegenbauer.jacobiCoefficient n k (k + p)
      else if q + 1 = p then
        Gegenbauer.jacobiCoefficient n k (k + q)
      else 0) * terminalIndicator (L - k) m q *
        terminalIndicator (L - k) m p
    change (∑ q : Fin (L - k + 1), g q.val) =
      ∑ q ∈ Finset.range (L - k + 1), g q
    exact Fin.sum_univ_eq_sum_range g (L - k + 1)
  simp_rw [hfin]
  rw [tridiagonal_quadratic_sum]
  rw [terminal_indicator_edge_sum (L - k) m hm]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  omega
end SpherePacking.SpectralAsymptotics

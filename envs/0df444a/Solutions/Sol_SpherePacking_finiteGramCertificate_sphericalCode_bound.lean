-- Prove2me | solution 1 for SpherePacking.finiteGramCertificate_sphericalCode_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/150df5be-712a-4aaa-8f96-9883cfb11313

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_finite_linear_programming_bound
import Theorems.Thm_SpherePacking_harmonicDimension_le_truncated
import Theorems.Thm_SpherePacking_isometricPackingKernel_nonneg
import Theorems.Thm_SpherePacking_isometricPackingKernel_diag
import Theorems.Thm_SpherePacking_isometricPackingKernel_trace_cauchy
import Theorems.Thm_SpherePacking_finiteGramCertificate_auxiliary_sum_lower

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
open Filter
open scoped BigOperators InnerProductSpace
namespace SpherePacking
theorem _root_.solution
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k ≤ L)
    (certificate : FiniteGramCertificate n k L)
    {s : ℝ} (hs : s ≤ 1)
    (hgap : s < Jacobi.topEigenvalue n k L)
    (C : SphericalCode n s) :
    (C.points.card : ℝ) ≤
      ((1 - s) / (Jacobi.topEigenvalue n k L - s)) *
        ((truncatedHarmonicDimension n k L : ℝ) /
          (Gegenbauer.fibreDimension n k : ℝ)) := by
  have hd : 0 < (Gegenbauer.fibreDimension n k : ℝ) := by
    exact_mod_cast Gegenbauer.fibreDimension_pos hn k
  have hDnat : 0 < truncatedHarmonicDimension n k L :=
    lt_of_lt_of_le
      (Gegenbauer.harmonicDimension_pos (by omega : 2 ≤ n) k)
      (harmonicDimension_le_truncated n k L hkl)
  have hD : 0 < (truncatedHarmonicDimension n k L : ℝ) := by
    exact_mod_cast hDnat
  have hgap' : 0 < Jacobi.topEigenvalue n k L - s :=
    sub_pos.mpr hgap
  have htrace :=
    isometricPackingKernel_trace_cauchy certificate.fibre C.points
  have hnormalized :
      (C.points.card : ℝ) ^ 2 *
          (Gegenbauer.fibreDimension n k : ℝ) ^ 2 /
          (truncatedHarmonicDimension n k L : ℝ) ≤
        ∑ x ∈ C.points, ∑ y ∈ C.points,
          isometricPackingKernel certificate.fibre x y := by
    apply (div_le_iff₀ hD).2
    nlinarith [htrace]
  have hpositive :
      (C.points.card : ℝ) ^ 2 *
        ((Jacobi.topEigenvalue n k L - s) *
          (Gegenbauer.fibreDimension n k : ℝ) ^ 2 /
          (truncatedHarmonicDimension n k L : ℝ)) ≤
        ∑ x ∈ C.points, ∑ y ∈ C.points,
          auxiliaryFiniteGramKernel certificate s x y := by
    calc
      (C.points.card : ℝ) ^ 2 *
          ((Jacobi.topEigenvalue n k L - s) *
            (Gegenbauer.fibreDimension n k : ℝ) ^ 2 /
            (truncatedHarmonicDimension n k L : ℝ)) =
        (Jacobi.topEigenvalue n k L - s) *
          ((C.points.card : ℝ) ^ 2 *
            (Gegenbauer.fibreDimension n k : ℝ) ^ 2 /
            (truncatedHarmonicDimension n k L : ℝ)) := by
          ring
      _ ≤ (Jacobi.topEigenvalue n k L - s) *
          (∑ x ∈ C.points, ∑ y ∈ C.points,
            isometricPackingKernel certificate.fibre x y) :=
          mul_le_mul_of_nonneg_left hnormalized hgap'.le
      _ ≤ ∑ x ∈ C.points, ∑ y ∈ C.points,
          auxiliaryFiniteGramKernel certificate s x y :=
        finiteGramCertificate_auxiliary_sum_lower certificate C
  have hc :
      0 < (Jacobi.topEigenvalue n k L - s) *
        (Gegenbauer.fibreDimension n k : ℝ) ^ 2 /
        (truncatedHarmonicDimension n k L : ℝ) :=
    div_pos (mul_pos hgap' (sq_pos_of_pos hd)) hD
  have hB :
      0 ≤ (1 - s) * (Gegenbauer.fibreDimension n k : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hs) hd.le
  have hdiag : ∀ x ∈ C.points,
      auxiliaryFiniteGramKernel certificate s x x ≤
        (1 - s) * (Gegenbauer.fibreDimension n k : ℝ) := by
    intro x hx
    simp [auxiliaryFiniteGramKernel, C.unit_norm x hx,
      isometricPackingKernel_diag]
  have hoff : ∀ x ∈ C.points, ∀ y ∈ C.points, x ≠ y →
      auxiliaryFiniteGramKernel certificate s x y ≤ 0 := by
    intro x hx y hy hxy
    unfold auxiliaryFiniteGramKernel
    exact mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (C.inner_le x hx y hy hxy))
      (isometricPackingKernel_nonneg certificate.fibre x y)
  have hbound := finite_linear_programming_bound C.points
    (auxiliaryFiniteGramKernel certificate s)
    hc hB hdiag hoff hpositive
  calc
    (C.points.card : ℝ) ≤
        ((1 - s) * (Gegenbauer.fibreDimension n k : ℝ)) /
          ((Jacobi.topEigenvalue n k L - s) *
            (Gegenbauer.fibreDimension n k : ℝ) ^ 2 /
            (truncatedHarmonicDimension n k L : ℝ)) := hbound
    _ = ((1 - s) / (Jacobi.topEigenvalue n k L - s)) *
        ((truncatedHarmonicDimension n k L : ℝ) /
          (Gegenbauer.fibreDimension n k : ℝ)) := by
      field_simp [hd.ne', hD.ne', hgap'.ne']
end SpherePacking

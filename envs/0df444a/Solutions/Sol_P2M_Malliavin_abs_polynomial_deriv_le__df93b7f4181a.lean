-- Prove2me | solution 1 for P2M_Malliavin_abs_polynomial_deriv_le__df93b7f4181a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:24.964984+00:00
-- url     : https://prove2.me/submissions/98ad4ddc-3e94-4e9b-9cdd-90fbf77bfff3

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_abs_polynomial_deriv_le

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {g : ℝ → ℝ}
namespace Malliavin
theorem _root_.solution (p : Polynomial ℝ) (x : ℝ) :
    |deriv (fun x ↦ p.eval x) x| ≤
      (coeffMass p + coeffMass p.derivative) * Real.exp (p.natDegree * |x|) :=
  (abs_polynomial_deriv_le p le_rfl x).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (coeffMass_nonneg _))
      (Real.exp_nonneg _))
end Malliavin

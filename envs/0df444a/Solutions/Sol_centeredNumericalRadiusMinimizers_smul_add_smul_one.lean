-- Prove2me | solution 1 for centeredNumericalRadiusMinimizers_smul_add_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:42:46.736388+00:00
-- url     : https://prove2.me/submissions/77b10c69-a54e-4524-9575-f3eee69f0ba1

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_centeredNumericalRadiusMinimizers_add_smul_one
import Theorems.Thm_centeredNumericalRadiusMinimizers_smul

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
omit [Nontrivial E]
theorem _root_.solution
    (A : E →L[ℂ] E) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    centeredNumericalRadiusMinimizers (a • A + b • 1) =
      (fun c : ℂ => a * c + b) '' centeredNumericalRadiusMinimizers A := by
  rw [centeredNumericalRadiusMinimizers_add_smul_one,
    centeredNumericalRadiusMinimizers_smul A ha, Set.image_image]

-- Prove2me | solution 1 for P2M_numericalRange_unitary_conjugate__eb4e389bbb52
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:09:36.583063+00:00
-- url     : https://prove2.me/submissions/7ce97c03-1f13-4313-80bc-01f0428a2c86

import Definitions.Def_Operator_NumericalRange_Adjoint
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Theorems.Thm_numericalRadius_adjoint
import Theorems.Thm_numericalRange_unitary_conjugate
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_numericalRadiusSeminorm_apply
import Theorems.Thm_numericalRadius_neg
attribute [local simp] mem_numericalRange
attribute [local simp] numericalRadiusSeminorm_apply
attribute [local simp] numericalRadius_neg


attribute [local simp] numericalRadius_adjoint

set_option autoImplicit false
open Complex
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution (A U : E →L[ℂ] E)
    (hU : U ∈ unitary (E →L[ℂ] E)) :
    numericalRange (U * A * U†) = numericalRange A := by
  simpa only [adjoint_adjoint] using
    numericalRange_unitary_conjugate A (U†) (Unitary.star_mem hU)

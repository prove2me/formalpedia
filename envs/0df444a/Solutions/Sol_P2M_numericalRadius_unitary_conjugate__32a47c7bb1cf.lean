-- Prove2me | solution 1 for P2M_numericalRadius_unitary_conjugate__32a47c7bb1cf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:37:43.998516+00:00
-- url     : https://prove2.me/submissions/05e2094e-0a3c-4c65-befd-def90b1924f8

import Definitions.Def_Operator_NumericalRange_Adjoint
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Theorems.Thm_P2M_numericalRange_unitary_conjugate__eb4e389bbb52

set_option autoImplicit false
open Complex
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution (A U : E →L[ℂ] E)
    (hU : U ∈ unitary (E →L[ℂ] E)) :
    numericalRadius (U * A * U†) = numericalRadius A := by
  unfold numericalRadius
  rw [numericalRange_unitary_conjugate' A U hU]

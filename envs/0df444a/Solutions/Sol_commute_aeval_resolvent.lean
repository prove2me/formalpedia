-- Prove2me | solution 1 for commute_aeval_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:11.906561+00:00
-- url     : https://prove2.me/submissions/3d0be90b-48ab-48a0-ada3-e4fabd002fe5

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Theorems.Thm_resolvent_mul_aeval_eq_eval_mul_resolvent_sub_aeval_divByMonic
import Theorems.Thm_aeval_mul_resolvent_eq_eval_mul_resolvent_sub_aeval_divByMonic

set_option autoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ resolventSet ℂ A) : Commute (Polynomial.aeval A p) (resolvent A z) := by
  rw [Commute]
  exact
    (aeval_mul_resolvent_eq_eval_mul_resolvent_sub_aeval_divByMonic A p hz).trans
      (resolvent_mul_aeval_eq_eval_mul_resolvent_sub_aeval_divByMonic A p hz).symm

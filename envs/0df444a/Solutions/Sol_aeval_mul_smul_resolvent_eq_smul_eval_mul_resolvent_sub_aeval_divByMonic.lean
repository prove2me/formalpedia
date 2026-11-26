-- Prove2me | solution 1 for aeval_mul_smul_resolvent_eq_smul_eval_mul_resolvent_sub_aeval_divByMonic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:37.486518+00:00
-- url     : https://prove2.me/submissions/6443cb03-265f-42a6-94c3-a70e33afda81

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Theorems.Thm_aeval_mul_resolvent_eq_eval_mul_resolvent_sub_aeval_divByMonic
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (p : Polynomial ℂ) {z : ℂ} (hz : z ∈ resolventSet ℂ A) (h : ℂ) :
    Polynomial.aeval A p * (h • resolvent A z) =
      (h * Polynomial.eval z p) • resolvent A z -
        h • Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)) := by
  rw [mul_smul_comm,
    aeval_mul_resolvent_eq_eval_mul_resolvent_sub_aeval_divByMonic A p hz]
  simp only [smul_sub, smul_smul]

-- Prove2me | solution 1 for aeval_mul_resolvent_eq_eval_mul_resolvent_sub_aeval_divByMonic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:37:26.47044+00:00
-- url     : https://prove2.me/submissions/dc2977fb-81cb-4a20-8c64-a6a435656d09

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (p : Polynomial ℂ) {z : ℂ} (hz : z ∈ resolventSet ℂ A) :
    Polynomial.aeval A p * resolvent A z =
      Polynomial.eval z p • resolvent A z -
        Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)) := by
  let q := p /ₘ (Polynomial.X - Polynomial.C z)
  have hpoly : Polynomial.C (Polynomial.eval z p) +
      q * (Polynomial.X - Polynomial.C z) = p := by
    rw [mul_comm]
    rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval p z]
    exact Polynomial.modByMonic_add_div p (Polynomial.X - Polynomial.C z)
  have hres : (algebraMap ℂ (E →L[ℂ] E) z - A) * resolvent A z = 1 := by
    calc
      (algebraMap ℂ (E →L[ℂ] E) z - A) * resolvent A z =
          (↑hz.unit : E →L[ℂ] E) * ↑hz.unit⁻¹ := by
        rw [spectrum.resolvent_eq hz, hz.unit_spec]
      _ = 1 := Units.mul_inv _
  conv_lhs => lhs; rw [← hpoly]
  simp only [map_add, map_mul, map_sub, Polynomial.aeval_C, Polynomial.aeval_X, add_mul,
    mul_assoc]
  rw [show A - algebraMap ℂ (E →L[ℂ] E) z =
      -(algebraMap ℂ (E →L[ℂ] E) z - A) by abel]
  rw [neg_mul, mul_neg, hres, mul_one]
  simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, q, sub_eq_add_neg]

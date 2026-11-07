-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicComplexEmbedding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:46:30.353204+00:00
-- url     : https://prove2.me/submissions/4a9cadc1-42e2-45cc-9792-dfc6d1f9a6da

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    Function.Injective (lpsOriginalCyclotomicComplexEmbedding p) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using AdjoinRoot.induction_on with
  | ih P =>
    rw [lpsOriginalCyclotomicComplexEmbedding,AdjoinRoot.lift_mk] at hx
    have h := minpoly.isIntegrallyClosed_dvd
      ((lpsOriginalCyclotomicComplexRoot_primitive p).isIntegral (Fact.out : p.Prime).pos) hx
    rw [← Polynomial.cyclotomic_eq_minpoly
      (lpsOriginalCyclotomicComplexRoot_primitive p) (Fact.out : p.Prime).pos] at h
    exact AdjoinRoot.mk_eq_zero.mpr h
end QEC.Coding.TannerLiftedProduct

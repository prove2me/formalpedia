-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalSubfield_eval__mem_0d401beef6d5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:27:36.283503+00:00
-- url     : https://prove2.me/submissions/cda09445-af31-406a-a078-69a3db07de94

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (R K : Type*) [CommRing R] [Field K] (f : R →+* K)
    (S : Subfield K) (hf : ∀ a, f a ∈ S) (x : K) (hx : x ∈ S)
    (P : Polynomial R) : P.eval₂ f x ∈ S := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [Polynomial.eval₂_add]
    exact S.add_mem hP hQ
  | monomial n a =>
    rw [Polynomial.eval₂_monomial]
    exact S.mul_mem (hf a) (S.pow_mem hx n)
end QEC.Coding.TannerLiftedProduct

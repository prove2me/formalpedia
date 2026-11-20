-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalLocalization_subfield_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:27:52.609205+00:00
-- url     : https://prove2.me/submissions/a9e4af41-5bb5-4048-aae3-db78fc06c1c6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (R A K : Type*) [CommRing R] [CommRing A] [Field K]
    [Algebra R A] (M : Submonoid R) [IsLocalization M A]
    (f : A →+* K) (S : Subfield K)
    (hf : ∀ a : R, f (algebraMap R A a) ∈ S) (x : A) : f x ∈ S := by
  obtain ⟨⟨a,b⟩,hx⟩ := IsLocalization.mk'_surjective M x
  rw [← hx]
  have hb : f (algebraMap R A b) ≠ 0 :=
    ((IsLocalization.map_units A b).map f).ne_zero
  have h := congrArg f (IsLocalization.mk'_spec A a b)
  rw [map_mul] at h
  rw [(eq_div_iff hb).mpr h]
  exact S.div_mem (hf a) (hf b)
end QEC.Coding.TannerLiftedProduct

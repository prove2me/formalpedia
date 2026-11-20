-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAdjoinRoot_surjective_subfield_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:31:24.23964+00:00
-- url     : https://prove2.me/submissions/e43dd92b-f6c5-48b2-9594-2cd4768b9ab1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalSubfield_eval__mem_0d401beef6d5

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (R K : Type*) [CommRing R] [Field K] (P : Polynomial R)
    (f : AdjoinRoot P →+* K) (hf : Function.Surjective f)
    (S : Subfield K) (hc : ∀ a : R, f (AdjoinRoot.of P a) ∈ S)
    (hx : f (AdjoinRoot.root P) ∈ S) : S = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a,rfl⟩ := hf x
  obtain ⟨Q,rfl⟩ := AdjoinRoot.mk_surjective a
  rw [← AdjoinRoot.aeval_eq,Polynomial.aeval_def,Polynomial.hom_eval₂]
  exact lpsOriginalSubfield_eval₂_mem R K
    (f.comp (algebraMap R (AdjoinRoot P))) S hc _ hx Q
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_adjoinJN_overJ_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:38:34.295167+00:00
-- url     : https://prove2.me/submissions/e816529e-9b3d-4976-9a3d-85964c5c7872

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueFractionMap_X
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalSubfield_eval__mem_0d401beef6d5
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAdjoinRoot_surjective_subfield_eq_top
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_integerBaseEval
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLocalization_subfield_mem
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := (lpsOriginalGaussMaximalResidueFractionMap N hN p q).toAlgebra
    IntermediateField.adjoin (FractionRing (Polynomial (ZMod p)))
      {lpsOriginalGaussMaximalResidueJN N hN p q} = ⊤ := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueFractionMap N hN p q).toAlgebra
  let L := IntermediateField.adjoin (FractionRing (Polynomial (ZMod p)))
    {lpsOriginalGaussMaximalResidueJN N hN p q}
  have hn : lpsOriginalGaussMaximalResidueJN N hN p q ∈ L :=
    IntermediateField.mem_adjoin_simple_self _ _
  have hj : lpsOriginalGaussMaximalResidueJ N hN p q ∈ L := by
    rw [← lpsOriginalGaussMaximalResidueFractionMap_X N hN p q]
    exact L.algebraMap_mem _
  let g : LPSOriginalGaussBase p →+* K :=
    (Ideal.Quotient.mk q).comp (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p))
  have hc : ∀ a : LPSOriginalGaussBase p, g a ∈ L.toSubfield := by
    intro a
    apply lpsOriginalLocalization_subfield_mem (Polynomial ℤ) (LPSOriginalGaussBase p)
      K (lpsOriginalGaussPrime p).primeCompl g L.toSubfield _ a
    intro P
    change (g.comp (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))) P ∈ L.toSubfield
    rw [lpsOriginalGaussMaximalResidue_integerBaseEval]
    exact lpsOriginalSubfield_eval₂_mem ℤ K (Int.castRingHom K) L.toSubfield
      (fun z => L.toSubfield.intCast_mem z) _ hj P
  have hs : L.toSubfield = ⊤ :=
    lpsOriginalAdjoinRoot_surjective_subfield_eq_top (LPSOriginalGaussBase p) K
      (lpsOriginalGaussPolynomial N hN p) (Ideal.Quotient.mk q)
      (Ideal.Quotient.mk_surjective) L.toSubfield hc hn
  apply IntermediateField.ext
  intro x
  change x ∈ L.toSubfield ↔ x ∈ (⊤ : IntermediateField (FractionRing (Polynomial (ZMod p))) K)
  rw [hs]
  simp
end QEC.Coding.TannerLiftedProduct

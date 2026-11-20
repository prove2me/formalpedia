-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_integerPolynomial_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:59:02.681999+00:00
-- url     : https://prove2.me/submissions/5715632d-ba4e-4249-af14-4a169635ea31

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_integerBaseEval


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (P : Polynomial ℤ) (hP : P ∉ lpsOriginalGaussPrime p) :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    IsUnit (P.eval₂ (Int.castRingHom (LPSOriginalGaussAffineOrder N hN p ⧸ q))
      (lpsOriginalGaussMaximalResidueJ N hN p q)) := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let g : LPSOriginalGaussBase p →+* K :=
    (Ideal.Quotient.mk q).comp (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p))
  let s : (lpsOriginalGaussPrime p).primeCompl := ⟨P,hP⟩
  have h : IsUnit (g (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) s)) :=
    (IsLocalization.map_units (LPSOriginalGaussBase p) s).map g
  change IsUnit ((g.comp (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))) P) at h
  rw [lpsOriginalGaussMaximalResidue_integerBaseEval] at h
  exact h
end QEC.Coding.TannerLiftedProduct

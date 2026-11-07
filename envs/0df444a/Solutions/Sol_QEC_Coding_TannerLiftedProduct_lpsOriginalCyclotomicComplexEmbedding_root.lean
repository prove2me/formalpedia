-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicComplexEmbedding_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:30:54.530311+00:00
-- url     : https://prove2.me/submissions/78ccc19d-c186-4482-ae0b-9d09e3666f83

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    lpsOriginalCyclotomicComplexEmbedding p (AdjoinRoot.root (Polynomial.cyclotomic p ℤ))=
      lpsOriginalCyclotomicComplexRoot p :=
  AdjoinRoot.lift_root _
end QEC.Coding.TannerLiftedProduct

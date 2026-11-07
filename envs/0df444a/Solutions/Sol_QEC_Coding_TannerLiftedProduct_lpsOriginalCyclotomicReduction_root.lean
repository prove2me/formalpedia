-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicReduction_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:46:32.693994+00:00
-- url     : https://prove2.me/submissions/7d31acfa-f318-4840-9496-d3f694c27d7e

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    lpsOriginalCyclotomicReduction p (AdjoinRoot.root (Polynomial.cyclotomic p ℤ))=1 :=
  AdjoinRoot.lift_root _
end QEC.Coding.TannerLiftedProduct

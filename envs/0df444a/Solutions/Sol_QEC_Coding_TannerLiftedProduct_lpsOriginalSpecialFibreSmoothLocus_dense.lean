-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreSmoothLocus_dense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:57:20.191499+00:00
-- url     : https://prove2.me/submissions/0a515f66-9b53-45a2-a70f-da8850e3c799

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSmoothSpecialFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreToPrimeField_locallyOfFinitePresentation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibre_reduced


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N)
    (hpN : ¬ p ∣ N) :
    Dense (lpsOriginalSpecialFibreSmoothLocus p N hN :
      Set (lpsOriginalSpecialFibre p N hN)) := by
  let := lpsOriginalSpecialFibreToPrimeField_locallyOfFinitePresentation p N hN
  let := lpsOriginalSpecialFibre_reduced N hN p hpN
  exact Scheme.Hom.dense_smoothLocus_of_perfectField
    (lpsOriginalSpecialFibreToPrimeField p N hN)
end QEC.Coding.TannerLiftedProduct

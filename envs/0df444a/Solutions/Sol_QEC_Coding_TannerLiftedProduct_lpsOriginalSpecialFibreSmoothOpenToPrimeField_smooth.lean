-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreSmoothOpenToPrimeField_smooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:28:13.900199+00:00
-- url     : https://prove2.me/submissions/bd46e967-f657-4d1c-a365-7be5dc9b5bb9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSmoothSpecialFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreToPrimeField_locallyOfFinitePresentation


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N) :
    Smooth (lpsOriginalSpecialFibreSmoothOpenToPrimeField p N hN) := by
  let := lpsOriginalSpecialFibreToPrimeField_locallyOfFinitePresentation p N hN
  let U := lpsOriginalSpecialFibreSmoothLocus p N hN
  change Smooth (U.ι ≫ lpsOriginalSpecialFibreToPrimeField p N hN)
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  exact U.ι_preimage_self
end QEC.Coding.TannerLiftedProduct

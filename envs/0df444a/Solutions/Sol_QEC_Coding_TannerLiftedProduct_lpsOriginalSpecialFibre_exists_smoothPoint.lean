-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibre_exists_smoothPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:00:30.698224+00:00
-- url     : https://prove2.me/submissions/08c67e23-fd9d-4890-9a6f-4172811533c0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSmoothSpecialFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibreSmoothLocus_dense
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibre_nonempty


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N)
    (hpN : ¬ p ∣ N) :
    ∃ x : lpsOriginalSpecialFibre p N hN,
      x ∈ lpsOriginalSpecialFibreSmoothLocus p N hN := by
  let := lpsOriginalSpecialFibre_nonempty p N hN
  exact (lpsOriginalSpecialFibreSmoothLocus_dense p N hN hpN).nonempty
end QEC.Coding.TannerLiftedProduct

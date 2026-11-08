-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalSpecialFibreSmoothOpen_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:28:15.488591+00:00
-- url     : https://prove2.me/submissions/3077ab2c-dc50-4a74-a210-2b417abc1065

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFlat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSmoothSpecialFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSpecialFibre_exists_smoothPoint

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N)
    (hpN : ¬ p ∣ N) :
    Nonempty (lpsOriginalSpecialFibreSmoothLocus p N hN).toScheme := by
  obtain ⟨x, hx⟩ := lpsOriginalSpecialFibre_exists_smoothPoint p N hN hpN
  exact ⟨⟨x, hx⟩⟩
end QEC.Coding.TannerLiftedProduct

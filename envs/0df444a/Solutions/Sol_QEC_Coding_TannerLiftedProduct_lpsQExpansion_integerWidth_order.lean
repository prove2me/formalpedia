-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQExpansion_integerWidth_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:33:31.748159+00:00
-- url     : https://prove2.me/submissions/dde4efba-68c0-494b-8742-3c67d74d48ad

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQExpansion_integerWidth

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ)
    (h1 : (1:ℝ)∈Γ.strictPeriods) (m : ℕ) (hm : 0 < m) (f : ModularForm Γ k) :
    (UpperHalfPlane.qExpansion (m:ℝ) f).order=m • (UpperHalfPlane.qExpansion 1 f).order := by
  rw [lpsQExpansion_integerWidth Γ k h1 m hm f,PowerSeries.order_expand]
end QEC.Coding.TannerLiftedProduct

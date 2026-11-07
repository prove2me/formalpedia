-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_dvd_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:19:11.712085+00:00
-- url     : https://prove2.me/submissions/faf20f06-460d-4cbb-9e52-a0636d78ab62

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidth_dvd_of_positive_zmultiple
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_integerPeriod
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_periods_generated
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_cast
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_positive


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (ρ : SL(2, ℤ)) :
    lpsOriginalCuspWidthNat N ρ ∣ N := by
  have hp := lpsOriginalCuspGroup_integerPeriod N ρ
  rw [lpsOriginalCuspGroup_periods_generated] at hp
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hp
  rw [lpsOriginalCuspWidthNat_cast] at hz
  exact lpsOriginalCuspWidth_dvd_of_positive_zmultiple _ _
    (lpsOriginalCuspWidthNat_positive N ρ) (Nat.pos_of_ne_zero (NeZero.ne N)) z hz
end QEC.Coding.TannerLiftedProduct

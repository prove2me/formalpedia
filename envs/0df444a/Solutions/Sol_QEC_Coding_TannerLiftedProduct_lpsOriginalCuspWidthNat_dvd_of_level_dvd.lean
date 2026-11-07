-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_dvd_of_level_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:30:56.395669+00:00
-- url     : https://prove2.me/submissions/74f0212e-9089-4c0b-a6c0-49ee1891e5eb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidth_dvd_of_positive_zmultiple
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_level_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_periods_generated
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_cast
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_positive


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) :
    lpsOriginalCuspWidthNat N ρ ∣ lpsOriginalCuspWidthNat M ρ := by
  have hp := Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup M ρ)
  have hg := Subgroup.mem_strictPeriods_iff.mp hp
  have hn := Subgroup.mem_strictPeriods_iff.mpr (lpsOriginalCuspGroup_level_le N M hNM ρ hg)
  rw [lpsOriginalCuspGroup_periods_generated] at hn
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hn
  rw [lpsOriginalCuspWidthNat_cast, lpsOriginalCuspWidthNat_cast] at hz
  exact lpsOriginalCuspWidth_dvd_of_positive_zmultiple _ _
    (lpsOriginalCuspWidthNat_positive N ρ) (lpsOriginalCuspWidthNat_positive M ρ) z hz
end QEC.Coding.TannerLiftedProduct

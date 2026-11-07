-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_dvd_of_orbit_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:47:02.267255+00:00
-- url     : https://prove2.me/submissions/2296815a-25eb-497b-9a84-4dfb0b307b44

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_periods_le_of_orbit_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_periods_generated
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_cast
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_positive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidth_dvd_of_positive_zmultiple


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2, ℤ)) (h : lpsOriginalCuspOrbit N ρ = lpsOriginalCuspOrbit N ρ') :
    lpsOriginalCuspWidthNat N ρ ∣ lpsOriginalCuspWidthNat N ρ' := by
  have hp := lpsOriginalCuspGroup_periods_le_of_orbit_eq N ρ ρ' h
    (Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup N ρ'))
  rw [lpsOriginalCuspGroup_periods_generated] at hp
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hp
  rw [lpsOriginalCuspWidthNat_cast, lpsOriginalCuspWidthNat_cast] at hz
  exact lpsOriginalCuspWidth_dvd_of_positive_zmultiple _ _
    (lpsOriginalCuspWidthNat_positive N ρ) (lpsOriginalCuspWidthNat_positive N ρ') z hz
end QEC.Coding.TannerLiftedProduct

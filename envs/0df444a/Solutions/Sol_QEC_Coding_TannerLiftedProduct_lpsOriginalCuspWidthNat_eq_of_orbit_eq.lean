-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_eq_of_orbit_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:50:53.14667+00:00
-- url     : https://prove2.me/submissions/bca8a203-7230-4ce3-9310-c35e33f70f00

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_dvd_of_orbit_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2, ℤ)) (h : lpsOriginalCuspOrbit N ρ = lpsOriginalCuspOrbit N ρ') :
    lpsOriginalCuspWidthNat N ρ = lpsOriginalCuspWidthNat N ρ' :=
  Nat.dvd_antisymm (lpsOriginalCuspWidthNat_dvd_of_orbit_eq N ρ ρ' h)
    (lpsOriginalCuspWidthNat_dvd_of_orbit_eq N ρ' ρ h.symm)
end QEC.Coding.TannerLiftedProduct

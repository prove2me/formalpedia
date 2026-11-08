-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0_product_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:06:47.432656+00:00
-- url     : https://prove2.me/submissions/bcbac687-85a6-4d1d-a5fc-8e695a2ed200

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) :
    CongruenceSubgroup.Gamma0 (N*p) ≤ CongruenceSubgroup.Gamma0 N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr
  exact dvd_trans (by exact_mod_cast Nat.dvd_mul_right N p)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ (N*p)).mp hγ)
end QEC.Coding.TannerLiftedProduct

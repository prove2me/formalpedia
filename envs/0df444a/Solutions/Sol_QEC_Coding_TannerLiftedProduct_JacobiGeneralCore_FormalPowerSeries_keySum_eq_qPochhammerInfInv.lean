-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.keySum_eq_qPochhammerInfInv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:55:53.954544+00:00
-- url     : https://prove2.me/submissions/0d2f3d32-2e61-4e3d-838e-cda7c9b8d732

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_keySum_eq_keySum_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_coeff_keySum_eq_coeff_qPochhammerInfInv

set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution (k : ℕ) : keySum (R := R) k = qPochhammerInfInv := by
  ext d
  rw [keySum_eq_keySum_zero k, ← keySum_eq_keySum_zero (R := R) (d + 1)]
  exact coeff_keySum_eq_coeff_qPochhammerInfInv (d + 1) d (Nat.lt_succ_self d)
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries

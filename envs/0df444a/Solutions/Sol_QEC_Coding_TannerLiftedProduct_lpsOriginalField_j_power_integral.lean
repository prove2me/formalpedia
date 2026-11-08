-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalField_j_power_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:46:51.229771+00:00
-- url     : https://prove2.me/submissions/2e3acac4-092d-462e-a88f-dc29af41fe68

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPowerPoleClearing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_j_power_clear_interior
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_integral_iff_noInteriorPole


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalJPowerClearingDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalJPowerClearingDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalJPowerClearingDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalJPowerClearingDictionary004
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (f : K)
    (hno : ∀ x : Q, lpsOriginalFilledJ N (Sum.inl x) ≠ 0 →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f) :
    ∃ k : ℕ, IsIntegral P ((algebraMap P K Polynomial.X)^k*f) := by
  obtain ⟨k,hk⟩ := lpsOriginalField_j_power_clear_interior N hpos hN f hno
  exact ⟨k, (lpsOriginalField_integral_iff_noInteriorPole N hpos hN _).mpr hk⟩
end QEC.Coding.TannerLiftedProduct

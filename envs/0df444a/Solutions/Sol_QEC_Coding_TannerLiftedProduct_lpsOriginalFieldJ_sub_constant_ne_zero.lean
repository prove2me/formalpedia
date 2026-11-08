-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFieldJ_sub_constant_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:07:56.856735+00:00
-- url     : https://prove2.me/submissions/217ef907-8bbc-48e6-9c50-8774809c2d8f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFieldIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary004
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
omit [NeZero N]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : ℂ) :
    algebraMap P K Polynomial.X - algebraMap ℂ K a ≠ 0 := by
  have hi : Function.Injective (algebraMap P K) :=
    (algebraMap J K).injective.comp (IsFractionRing.injective P J)
  have hc : algebraMap P K (Polynomial.C a) = algebraMap ℂ K a := rfl
  rw [←hc,←map_sub]
  exact fun hz => Polynomial.X_sub_C_ne_zero a (hi (hz.trans (map_zero _).symm))
end QEC.Coding.TannerLiftedProduct

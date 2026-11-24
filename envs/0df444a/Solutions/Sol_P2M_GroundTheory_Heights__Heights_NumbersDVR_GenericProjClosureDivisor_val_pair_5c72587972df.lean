-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_val_pair_5c72587972df
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:47.444851+00:00
-- url     : https://prove2.me/submissions/ad774e22-e745-414d-ab91-485238cb562e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {N M M' : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
  {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
variable [∀ k, Fintype (ι k)]
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] [Algebra O Ω] [IsScalarTower O Ω Φ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
theorem _root_.solution {z : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ} {L : ℕ}
    {xs : Fin L → MRing (bundleIdx (bundleIdx ι M) M') O} {v : Fin L → Φ} (hxs : ∀ l, aeval z (xs l) = v l)
    (G : Fin L → MRing (bundleIdx (bundleIdx ι M) M') O) {x : MRing (bundleIdx (bundleIdx ι M) M') O} {w : Φ}
    (hx : aeval z x = w) (H : MRing (bundleIdx (bundleIdx ι M) M') O)
    (hval : aeval z H * w = ∑ l, aeval z (G l) * v l) :
    aeval z (∑ l, xs l * G l) = aeval z (x * H) := by
  rw [map_sum, map_mul, hx, mul_comm, hval]
  exact Finset.sum_congr rfl fun l _ => by rw [map_mul, hxs, mul_comm]
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor

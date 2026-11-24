-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_pointIdeal_algebraMap_218307a49609
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:03.579496+00:00
-- url     : https://prove2.me/submissions/47c9045d-3860-4b8d-b740-af84ccc818ae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureBirational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K : Type*} {ι : K → Type*} {O Ω Φ : Type*} [CommRing O] [Field Ω] [Field Φ]
    [Algebra O Ω] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ] (y : (Σ k, ι k) → Ω) :
    pointIdeal O (fun p => algebraMap Ω Φ (y p)) = pointIdeal O y := by
  have key : ∀ f, pointConeMap O (fun p => algebraMap Ω Φ (y p)) f =
      MvPolynomial.map (algebraMap Ω Φ) (pointConeMap O y f) := by
    intro f
    have h : (pointConeMap O (fun p => algebraMap Ω Φ (y p))).toRingHom =
        (MvPolynomial.map (algebraMap Ω Φ)).comp (pointConeMap O y).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [pointConeMap, IsScalarTower.algebraMap_apply O Ω Φ]
      · intro v
        simp [pointConeMap]
    have := RingHom.congr_fun h f
    simpa using this
  ext f
  simp only [pointIdeal, RingHom.mem_ker, key]
  exact ⟨fun h => map_injective _ (algebraMap Ω Φ).injective (by rw [h, map_zero]),
    fun h => by rw [h, map_zero]⟩
end GroundTheory.Heights₂.Heights.NumbersDVR

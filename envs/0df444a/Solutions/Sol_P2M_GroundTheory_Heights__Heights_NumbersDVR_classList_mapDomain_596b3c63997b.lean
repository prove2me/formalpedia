-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_mapDomain_596b3c63997b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:41:36.47374+00:00
-- url     : https://prove2.me/submissions/835fc0ef-565e-4000-abcf-a6dfe841ca28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra

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
open MvPolynomial
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {σ τ : Type*} (cls : τ → K → ℤ) (φ : σ → τ) (μ : σ →₀ ℕ) :
    classList cls (μ.mapDomain φ) = classList (cls ∘ φ) μ := by
  unfold classList
  congr 1
  rw [← Finsupp.toMultiset_map μ φ, Multiset.map_map]
end GroundTheory.Heights₂.Heights.NumbersDVR

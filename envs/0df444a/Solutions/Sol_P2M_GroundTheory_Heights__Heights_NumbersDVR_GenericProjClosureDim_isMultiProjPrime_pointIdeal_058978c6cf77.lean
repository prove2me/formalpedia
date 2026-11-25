-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_isMultiProjPrime_pointIdeal_058978c6cf77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:24:23.32178+00:00
-- url     : https://prove2.me/submissions/580d3d2e-0c9b-42ba-b08d-aa9ed889ad0e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDvrConeDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairBundleTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_coneMap_component_ae8cbcbece31

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
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDim
variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L] {K : Type*} [DecidableEq K]
  {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDim
theorem _root_.solution (z : (Σ k, ι k) → L) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    IsMultiProjPrime (pointIdeal R z) := by
  refine ⟨RingHom.ker_isPrime _, ?_, ?_⟩
  · intro f hf b
    rw [pointIdeal, RingHom.mem_ker] at hf ⊢
    have := coneMap_component (R := R) z b f
    rw [hf, map_zero] at this
    exact this.symm
  · intro k
    obtain ⟨i, hi⟩ := hz k
    refine ⟨i, ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    change pointConeMap R z (X ⟨k, i⟩) ≠ 0
    rw [pointConeMap, aeval_X]
    exact mul_ne_zero (by simpa using hi) (X_ne_zero _)
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDim

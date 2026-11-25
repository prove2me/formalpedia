-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PointIdealMultiProj_coneMap_component_2a817bc13b72
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:25:20.055839+00:00
-- url     : https://prove2.me/submissions/6b5ec7a1-4da5-4c2d-8179-fb80c57b4c65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPointIdealMultiProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPointIdealMultiProj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PointIdealMultiProj_coneMap_monomial_isWeightedHomogeneous_3f0ae37a1420

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
open GroundTheory.Heights₂.Heights.NumbersDVR.PointIdealMultiProj
variable {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L]
  {K : Type*} [DecidableEq K] {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.PointIdealMultiProj
theorem _root_.solution (z : (Σ k, ι k) → L) (b : K → ℕ) (f : MRing ι F) :
    weightedHomogeneousComponent (coneWeight K) b (pointConeMap F z f) =
      pointConeMap F z (weightedHomogeneousComponent (blockWeight ι) b f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 := coneMap_monomial_isWeightedHomogeneous (K := K) (F := F) z d a
    have h2 : IsWeightedHomogeneous (blockWeight ι) (monomial d a : MRing ι F)
        (Finsupp.weight (blockWeight ι) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : b = Finsupp.weight (blockWeight ι) d
    · subst h
      rw [h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]
    · rw [h1.weightedHomogeneousComponent_ne _ h, h2.weightedHomogeneousComponent_ne _ h, map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
end GroundTheory.Heights₂.Heights.NumbersDVR.PointIdealMultiProj

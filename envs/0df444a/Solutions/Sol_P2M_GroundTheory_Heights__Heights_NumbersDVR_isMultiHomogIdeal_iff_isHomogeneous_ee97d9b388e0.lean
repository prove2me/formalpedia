-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_iff_isHomogeneous_ee97d9b388e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:12.695998+00:00
-- url     : https://prove2.me/submissions/d3d94ee5-8331-49db-b7ce-514a30b4e90c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPrimeFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_decompose_blockWeight_8e63e41e72c9

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
universe u
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K]
    {ι : K → Type*} (I : Ideal (MRing ι R)) :
    IsMultiHomogIdeal I ↔ I.IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) := by
  constructor
  · intro h b r hr
    rw [decompose_blockWeight]
    exact h r hr b
  · intro h r hr b
    rw [← decompose_blockWeight]
    exact h b hr
end GroundTheory.Heights₂.Heights.NumbersDVR

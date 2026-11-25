-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_localLattice_swapAt_fbff93b7be3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:47:45.406903+00:00
-- url     : https://prove2.me/submissions/063faf2d-c64d-4521-ad0c-3e78b220cc7c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsExamples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_localLattice_baseChange_37285dfb9883
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_swapCoord_standard_1189ac811217

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (v₀ v : HeightOneSpectrum (𝓞 K)) :
    (localLattice v (FullLattice.standard K 2).carrier : Set _) =
      swapAt v₀ v '' localLattice v (FullLattice.standard K 2).carrier := by
  by_cases h : v = v₀
  · simp only [swapAt, if_pos h]
    exact localLattice_baseChange v swapCoord _ swapCoord_standard
  · simp only [swapAt, if_neg h, LinearEquiv.coe_one, Set.image_id]
end GroundTheory.Heights₂.Heights

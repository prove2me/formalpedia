-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogNormEnergyDensNonneg_proof_333b72926e75
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:03:47.759956+00:00
-- url     : https://prove2.me/submissions/7160a12b-1d75-4fea-98f5-73f3003a5ece

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogNormEnergyDensNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogNormGradDensNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogNormEnergyDensNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogNormGradDensNonneg_proof_7c7673e23d37
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceSectionMass_proof_139e377538c6


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
namespace GroundTheory.Heights₂.Heights
namespace LogNormEnergyDensNonneg
theorem _root_.solution : LogNormEnergyDensNonneg.Statement := by
  intro n d h s y v hs hsy
  exact LogNormGradDensNonneg.proof n d h s y v hs hsy
end LogNormEnergyDensNonneg
end GroundTheory.Heights₂.Heights

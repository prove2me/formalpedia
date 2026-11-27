-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardMean_proof_ce8497b1279f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:04:01.005057+00:00
-- url     : https://prove2.me/submissions/28a4f03f-743c-4a39-a001-69f0cec5c855

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardMean
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_HadamardMean_intersectionNumber_baseChange_c763fd917cd9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField Matrix GroundTheory.Heights₂.Heights
noncomputable section
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace HadamardMean
theorem _root_.solution (_h1 : Sublattice.Statement) : HadamardMean.Statement :=
  HadamardMean.intersectionNumber_baseChange
end HadamardMean
end GroundTheory.Heights₂.Heights.LatticeLemmas

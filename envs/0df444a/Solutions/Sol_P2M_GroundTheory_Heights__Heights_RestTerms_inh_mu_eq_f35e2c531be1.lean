-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_inh_mu_eq_f35e2c531be1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:01.225153+00:00
-- url     : https://prove2.me/submissions/094585cf-a420-4d9f-9685-1a92abc4e4cb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants

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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
noncomputable section
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution : smallBlockMu 1 1 1 .last = flagTwoSecondRoot := by
  simp [smallBlockMu, yRoot, yIndex, SmallBlock.sign]
end GroundTheory.Heights₂.Heights.RestTerms

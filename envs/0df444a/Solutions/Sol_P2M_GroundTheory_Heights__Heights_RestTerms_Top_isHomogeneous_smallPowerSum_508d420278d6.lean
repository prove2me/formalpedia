-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_smallPowerSum_508d420278d6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:46.278884+00:00
-- url     : https://prove2.me/submissions/6e4abfb5-65b0-4493-baee-9e44bffc6e29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_yRoot_d0d8d9eadb63

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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (f r a : ℕ) (c : SmallBlock) (k : ℕ) (τ : Fin f) :
    (smallPowerSum f r a c k τ).IsHomogeneous k := by
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  simpa using (isHomogeneous_yRoot f r a c τ i).pow k
end GroundTheory.Heights₂.Heights.RestTerms.Top

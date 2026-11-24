-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Section2_hypotheses_inhabited_2342196bac3b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:46.979796+00:00
-- url     : https://prove2.me/submissions/cd912898-95a1-4051-bf77-3771c25fddf4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements

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
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace Section2
theorem _root_.solution :
    1 ≤ 2 ∧ 1 ≤ 1 ∧ (1 : Fin 2) ≠ 0 ∧ 2 ≤ 1 + 1 := by decide
end Section2
end GroundTheory.Heights₂.Heights.RestTerms

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_LemmaA_hypotheses_inhabited_db910e8699fe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:50.014387+00:00
-- url     : https://prove2.me/submissions/107a88cf-13f3-421f-b3ae-82a10eb4378c

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
namespace LemmaA
theorem _root_.solution :
    IsPowerSumDecomposition 1 1 (blockPowerSum 1 1 1 0)
        (fun k τ => if k = 1 ∧ τ = 0 then 1 else 0) ∧
      (1 : RootRing 1 1).IsHomogeneous (1 - 1) := by
  refine ⟨?_, isHomogeneous_one _ _⟩
  simp [IsPowerSumDecomposition]
end LemmaA
end GroundTheory.Heights₂.Heights.RestTerms

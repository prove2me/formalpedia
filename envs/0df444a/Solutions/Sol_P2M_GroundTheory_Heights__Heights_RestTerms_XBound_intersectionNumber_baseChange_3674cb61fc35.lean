-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_XBound_intersectionNumber_baseChange_3674cb61fc35
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:51:08.363468+00:00
-- url     : https://prove2.me/submissions/c5862c71-c236-40ba-8d1a-cadcadc219aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary

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
open Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace XBound
theorem _root_.solution : XBound.Statement := by
  intro r a hN
  have hN' : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast hN
  refine ⟨?_, ?_⟩
  · simp only [restX]
    push_cast
    push_cast at hN'
    nlinarith [sq_nonneg ((r : ℝ) - a)]
  · nlinarith
end XBound
end GroundTheory.Heights₂.Heights.RestTerms

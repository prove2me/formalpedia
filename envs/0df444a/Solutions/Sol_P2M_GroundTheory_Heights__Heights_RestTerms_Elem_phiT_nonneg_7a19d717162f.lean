-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Elem_phiT_nonneg_7a19d717162f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:05.408831+00:00
-- url     : https://prove2.me/submissions/d659b296-3e87-4bb2-8329-07c1e7ea1707

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt

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
open GroundTheory.Heights₂.Heights.RestTerms.Elem
namespace GroundTheory.Heights₂.Heights.RestTerms.Elem
theorem _root_.solution {t : ℝ} (ht : 1 ≤ t) : 0 ≤ phiT t := by
  unfold phiT
  have := Real.log_nonneg ht
  positivity
end GroundTheory.Heights₂.Heights.RestTerms.Elem

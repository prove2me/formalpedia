-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_some_4a0cbc5e102b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:37.020808+00:00
-- url     : https://prove2.me/submissions/d315e9da-d45e-4ae3-b0b4-2110bb85635a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (c : K → ℤ) (k : K) :
    pullDeg Function.Embedding.some c (some k) = c k :=
  (Function.Embedding.some (α := K)).injective.extend_apply c 0 k
end GroundTheory.Heights₂.Heights.FieldNumbers

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_tendsto_restrict_2aee757d54c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:54:11.30929+00:00
-- url     : https://prove2.me/submissions/42c9bc75-1370-4d7e-82e3-7ba1bed4dd48

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
theorem _root_.solution :
    Tendsto (fun m : Option K → ℤ => fun k => m (some k)) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨fun o => Option.elim o 0 b, fun _ ha k => ha (some k)⟩
end GroundTheory.Heights₂.Heights.FieldNumbers

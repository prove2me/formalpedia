-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_eventually_none_ge_1e277cebb144
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:30.407307+00:00
-- url     : https://prove2.me/submissions/e372c3d4-2751-4b18-92cc-da769267c5d2

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
theorem _root_.solution (a : ℤ) : ∀ᶠ m : Option K → ℤ in atTop, a ≤ m none :=
  (eventually_ge_atTop (fun _ : Option K => a)).mono fun _ hm => hm none
end GroundTheory.Heights₂.Heights.FieldNumbers

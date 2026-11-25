-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_foldr_diffStep_eventuallyEq_175d47ef4cd0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:40.873137+00:00
-- url     : https://prove2.me/submissions/51a3eca3-a424-48ac-8ebd-99a0d4b23e2e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMultEqualsCoeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_tendsto_sub_64f66200b3cd

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
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MultEqualsCoeff
variable {K : Type*}
namespace GroundTheory.Heights₂.Heights.FieldNumbers.MultEqualsCoeff
theorem _root_.solution {h g : (K → ℤ) → ℤ} (e : h =ᶠ[atTop] g) :
    ∀ L : List (K → ℤ), L.foldr diffStep h =ᶠ[atTop] L.foldr diffStep g
  | [] => e
  | b :: L => by
      have e' := solution e L
      filter_upwards [e', (tendsto_sub b).eventually e'] with m h1 h2
      simp only [List.foldr_cons, diffStep]
      rw [h1, h2]
end GroundTheory.Heights₂.Heights.FieldNumbers.MultEqualsCoeff

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_eventualValue_precomp_081848f07677
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:23:59.379342+00:00
-- url     : https://prove2.me/submissions/be1d7d6f-ea0d-463c-b669-1fd807f22ab2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_eventualValue_congr_ad72207f60cd

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
open GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)
namespace GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
theorem _root_.solution (g : (K₁ → ℤ) → ℤ) :
    eventualValue (fun m : K₂ → ℤ => g (m ∘ e)) = eventualValue g := by
  refine eventualValue_congr fun c => ?_
  rw [← (precompOrderIso e).map_atTop, Filter.eventually_map]
  rfl
end GroundTheory.Heights₂.Heights.FieldNumbers.Relabel

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_fg_span_of_le_88db96d6e48a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:54.164378+00:00
-- url     : https://prove2.me/submissions/b0ff70fb-ecf8-40eb-b540-92e61c19062f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundleLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_span_span_of_le_5980be65a218

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open scoped Pointwise
variable {S : Type*} [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω]
variable {A B : Subalgebra S Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution (hAB : A ≤ B) {L : Submodule A Ω} (hL : L.FG) :
    (Submodule.span B (L : Set Ω)).FG := by
  obtain ⟨T, rfl⟩ := hL
  rw [span_span_of_le hAB]
  exact Submodule.fg_span T.finite_toSet
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

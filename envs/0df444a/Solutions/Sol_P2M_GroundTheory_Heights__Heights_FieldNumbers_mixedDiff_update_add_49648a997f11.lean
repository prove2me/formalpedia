-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_update_add_49648a997f11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:12:45.931509+00:00
-- url     : https://prove2.me/submissions/2d1d6d89-aef8-4034-97c5-94e413dbed70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_diffStep_set_add_8aefba410a42
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ofFn_update_64c49455c3c2

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
open GroundTheory.Heights₂.Heights.NumbersDVR
universe u
variable {K : Type*}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {n : ℕ} (bs : Fin n → K → ℤ) (i : Fin n) (b b' : K → ℤ)
    (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    mixedDiff (Function.update bs i (b + b')) h m =
      mixedDiff (Function.update bs i b) h m + mixedDiff (Function.update bs i b') h (m - b) := by
  simp only [mixedDiff, ofFn_update]
  exact foldr_diffStep_set_add h b b' _ i (by simp) m
end GroundTheory.Heights₂.Heights.FieldNumbers

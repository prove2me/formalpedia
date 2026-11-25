-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_coord_zero_b5ada36f56e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:12:11.051408+00:00
-- url     : https://prove2.me/submissions/b364906f-60c4-42dd-84e9-6a641d720c03

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumZeroSlot
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_diffStep_eq_zero_of_mem_e34c1b7dec2b

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
open GroundTheory.Heights₂.Heights.NumbersDVR Filter
universe u
variable {K : Type*}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {n : ℕ} (bs : Fin n → K → ℤ) (i : Fin n) (hi : bs i = 0)
    (h : (K → ℤ) → ℤ) : mixedDiff bs h = 0 :=
  foldr_diffStep_eq_zero_of_mem _ (List.mem_ofFn.mpr ⟨i, hi⟩) h
end GroundTheory.Heights₂.Heights.FieldNumbers

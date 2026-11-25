-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumZeroSlot_proof_c5f44b3a0cb0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:51.895546+00:00
-- url     : https://prove2.me/submissions/2e6dfdca-6971-4d37-87ab-aa6201730fa0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumZeroSlot
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_coord_zero_b5ada36f56e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_eventually_zero_ad5ec0bf8dbd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_eventualValue_eq_zero_12cccfe72c95
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_nat_of_le_of_lt_4b1524a9290b

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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace IntNumZeroSlot
theorem _root_.solution (h₁ : MixedDiffConst.Statement.{u})
    (h₂ : HilbEventuallyPoly.Statement.{u}) (h₃ : HilbDegreeBound.Statement.{u}) :
    IntNumZeroSlot.Statement.{u} := by
  intro F _ K _ _ ι _ I
  refine ⟨fun n bs i hi => ?_, fun hI n bs hn => ?_⟩
  · unfold intNum
    refine eventualValue_eq_zero (Eventually.of_forall fun m => ?_)
    rw [mixedDiff_coord_zero bs i hi]
    rfl
  · unfold intNum
    apply eventualValue_eq_zero
    by_cases hR : IsRelevant I
    · by_cases hd : ∃ d : ℕ, relDim I = d
      · obtain ⟨d, hd⟩ := hd
        have hdn : d < n := by
          rw [hd] at hn
          exact_mod_cast hn
        exact (h₁ F K ι I hI hR d hd).2 n hdn bs
      · obtain ⟨p, hp⟩ := h₂ F K ι I hI
        have hp0 : p = 0 := by
          by_contra hne
          exact hd (exists_nat_of_le_of_lt ((h₃ F K ι I hI).1 hR p hp hne) hn)
        apply mixedDiff_eventually_zero
        filter_upwards [hp] with m hm
        rw [hp0, map_zero] at hm
        exact_mod_cast hm
    · exact mixedDiff_eventually_zero bs ((h₃ F K ι I hI).2 hR)
end IntNumZeroSlot
end GroundTheory.Heights₂.Heights.FieldNumbers

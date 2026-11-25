-- Prove2me | solution 1 for PI.SqPair.LCP.inert_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:22:44.82438+00:00
-- url     : https://prove2.me/submissions/e1868ac3-8a79-4413-85b0-8fe972f1b0b4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
open PI.SqPair.LocCartanPairW
namespace PI.SqPair.LCP
theorem _root_.solution {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R} {ϖ : R}
    (hI : Inert R₀ ϖ) : IsLocalRing R := by
  haveI := hI.dom
  have key : ∀ x : R, ¬ IsUnit x → ϖ ∣ x := by
    intro x hx
    by_cases h0 : x = 0
    · exact ⟨0, by rw [h0, mul_zero]⟩
    · obtain ⟨m, u, hu, rfl⟩ := hI.val x h0
      cases m with
      | zero => exact absurd (by simpa using hu) hx
      | succ k => exact ⟨ϖ ^ k * u, by ring⟩
  have back : ∀ x : R, ϖ ∣ x → ¬ IsUnit x := by
    rintro x ⟨c, rfl⟩ hu
    exact hI.pi_nonunit (isUnit_of_mul_isUnit_left hu)
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  exact back _ (dvd_add (key a ha) (key b hb))
end PI.SqPair.LCP

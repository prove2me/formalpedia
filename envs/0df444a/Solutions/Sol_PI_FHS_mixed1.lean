-- Prove2me | solution 1 for PI.FHS.mixed1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:22.012114+00:00
-- url     : https://prove2.me/submissions/b6aba9b6-41b2-4413-9e72-6da0b81f160d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix FockH1Action
open PI PI.FHS
variable {p q r s : ℕ}
namespace PI.FHS
theorem _root_.solution {Z : Mat p q} (hZ : IsPC Z) :
    Mixed (Matrix.kroneckerMap (fun a b => a * b) Z (1 : Mat r s)) := by
  rintro ⟨a, c⟩ ⟨b, d⟩ hne
  simp only [Matrix.kroneckerMap_apply] at hne
  by_cases hcd : c = d
  · subst hcd
    have hs : ¬ FockH1Action.sameBlock a b := fun hab => hne (by rw [hZ a b hab, zero_mul])
    clear hne hZ
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp_all [FockH1Action.sameBlock, FockH1Action.linePos]
  · exact absurd (by rw [Matrix.one_apply_ne hcd, mul_zero]) hne
end PI.FHS

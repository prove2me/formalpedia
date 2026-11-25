-- Prove2me | solution 1 for PI.FHS.mixed2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:27.032267+00:00
-- url     : https://prove2.me/submissions/93084302-faf9-4432-86fd-cad488c083a0

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
theorem _root_.solution {Z : Mat r s} (hZ : IsPC Z) :
    Mixed (Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Z) := by
  rintro ⟨a, c⟩ ⟨b, d⟩ hne
  simp only [Matrix.kroneckerMap_apply] at hne
  by_cases hab : a = b
  · subst hab
    have hs : ¬ FockH1Action.sameBlock c d := fun hcd => hne (by rw [hZ c d hcd, mul_zero])
    clear hne hZ
    rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
      simp_all [FockH1Action.sameBlock, FockH1Action.linePos]
  · exact absurd (by rw [Matrix.one_apply_ne hab, zero_mul]) hne
end PI.FHS

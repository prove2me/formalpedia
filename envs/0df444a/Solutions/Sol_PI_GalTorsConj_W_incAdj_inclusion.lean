-- Prove2me | solution 1 for PI.GalTorsConj.W.incAdj_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:24:23.106344+00:00
-- url     : https://prove2.me/submissions/688c1ff3-f99b-4899-9277-97ff2f14d49e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_IncAdjInclusion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Polynomial
namespace PI.GalTorsConj.W
theorem _root_.solution (M M₁ : IntermediateField ℚ ℂ) (h : M ≤ M₁) (x : M) :
    incAdj M M₁ (IntermediateField.inclusion h x) = algebraMap M _ x := Subtype.ext rfl
end PI.GalTorsConj.W

-- Prove2me | solution 1 for PI.SqPairLocal.isLattice_of_isSDG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:27:40.650166+00:00
-- url     : https://prove2.me/submissions/33611d73-43cf-4372-b779-dd6c6da0f770

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnimodGenus
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnimodularOfIsSDG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG PI.UG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PI.SqPairLocal
theorem _root_.solution {N : ℕ} {L : Submodule (𝓞 E) (Fin N → E)} (h : IsSDG E N L) :
    Submodule.IsLattice E L := by
  obtain ⟨h1, h2, -⟩ := h
  exact ⟨h1, h2⟩
end PI.SqPairLocal

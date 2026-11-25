-- Prove2me | solution 1 for PI.ArtSch.Glue.frob_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:28.990813+00:00
-- url     : https://prove2.me/submissions/762e5177-7ed7-4338-976a-a61c97a15b36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationGluing_ValbLeOfCoeffEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch PI.ArtSch.Glue
open scoped NNReal
noncomputable section
variable {l : ℕ} [hl : Fact l.Prime]
namespace PI.ArtSch.Glue
theorem _root_.solution (hR : RootModP) : Function.Surjective (frobenius (ModP (OC l) l) l) := by
  intro b
  obtain ⟨z, hz⟩ := hR l 0 b
  exact ⟨z, by rw [frobenius_def]; linear_combination hz⟩
end PI.ArtSch.Glue

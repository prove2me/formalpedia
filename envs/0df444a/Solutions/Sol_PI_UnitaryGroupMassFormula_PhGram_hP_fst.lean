-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.hP_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:41:17.519414+00:00
-- url     : https://prove2.me/submissions/1fc7fabb-10de-4c8f-83de-a38289970fe9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_PhGramOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_Assemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhGram
open PI.FglGram
variable {p : ℕ} [Fact p.Prime]
namespace PI.UnitaryGroupMassFormula.PhGram
theorem _root_.solution {κ : Type*} [Fintype κ] (x y : κ → ℂ_[p] × ℂ_[p]) :
    (hP x y).1 = ∑ i, (x i).1 * (y i).2 := by
  unfold hP
  rw [Prod.fst_sum]
  rfl
end PI.UnitaryGroupMassFormula.PhGram

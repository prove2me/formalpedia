-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.good_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:08.588221+00:00
-- url     : https://prove2.me/submissions/73f33594-9cfb-46c5-a505-faee6d142363

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
theorem _root_.solution {σ : Type*} (i : σ) : Good (Xv (p := p) i) := by
  unfold Good
  refine ⟨by simp [PI.FglGram.Xv], ?_⟩
  unfold PI.FglGram.IntegralMv
  intro n
  unfold PI.FglGram.IsIntP
  unfold PI.FglGram.Xv
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp
end PI.UnitaryGroupMassFormula.PhGram

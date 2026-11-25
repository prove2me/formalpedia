-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.ExpandW.rhsBy_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:41:13.685238+00:00
-- url     : https://prove2.me/submissions/3b52b8ef-d341-41f9-8025-948ad7186f5c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_Expand

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhGram PI.UnitaryGroupMassFormula.PhGram.ExpandW
open PI.FglGram PI.UnitaryGroupMassFormula.PhGram
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]} {σ : Type}
namespace PI.UnitaryGroupMassFormula.PhGram.ExpandW
theorem _root_.solution {m : ℕ} (a : Fin (m + 1) → MvPowerSeries σ ℂ_[p]) :
    rhsBy l ex ph a = rhsBy l ex ph (fun j : Fin m => a (Fin.castSucc j)) +
      (phAt ph (a (Fin.last m)) + ∑ j : Fin m, be l ex ph (a (Fin.castSucc j)) (a (Fin.last m))) := by
  unfold rhsBy
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.sum_univ_castSucc]
    simp [Fin.castSucc_lt_castSucc_iff, (Fin.castSucc_lt_last k).asymm]
  · rw [Fin.sum_univ_castSucc]
    simp [Fin.castSucc_lt_last]
end PI.UnitaryGroupMassFormula.PhGram.ExpandW

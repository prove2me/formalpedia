-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.ExpandW.rhsBy_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:18.825593+00:00
-- url     : https://prove2.me/submissions/28d953d0-d569-4020-bc0c-c2dab9123cf8

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
theorem _root_.solution {m : ℕ} (a : Fin m → MvPowerSeries σ ℂ_[p]) :
    rhsBy l ex ph a = ∑ j, phAt ph (a j) +
      ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), be l ex ph (a j) (a j') := by
  unfold rhsBy
  rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun j' j => if j < j' then be l ex ph (a j) (a j') else 0)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_filter]
end PI.UnitaryGroupMassFormula.PhGram.ExpandW

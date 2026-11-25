-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.ExpandW.good_pt_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:07:36.198874+00:00
-- url     : https://prove2.me/submissions/e1531606-9742-4d82-8ea1-d301356e46b2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_Expand
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_good_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_pt_sum_succ
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_pt_sum_zero

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
theorem _root_.solution (hGA : GoodAdd) {S : Set (ℂ_[p] × ℂ_[p])} (H : Hyps l ex ph S) {m : ℕ}
    (a : Fin m → MvPowerSeries σ ℂ_[p]) (ha : ∀ j, Good (a j)) : Good (pt ex (∑ j, lg l (a j))) := by
  induction m with
  | zero =>
    rw [pt_sum_zero H.data]
    exact good_zero
  | succ m ih =>
    rw [pt_sum_succ H.data a (fun j => (ha j).1)]
    exact hGA p l ex ph S H σ _ _ (ih (fun j => a (Fin.castSucc j)) (fun j => ha _)) (ha _)
end PI.UnitaryGroupMassFormula.PhGram.ExpandW

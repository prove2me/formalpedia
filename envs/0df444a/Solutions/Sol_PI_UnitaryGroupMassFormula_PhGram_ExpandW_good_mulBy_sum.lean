-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.ExpandW.good_mulBy_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:43:22.332496+00:00
-- url     : https://prove2.me/submissions/5ebc29cd-4846-4b46-adf8-a5cf58fff75c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_Expand
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_mulBy_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_mulBy_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_ExpandW_good_zero

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
theorem _root_.solution (hGA : GoodAdd) {S : Set (ℂ_[p] × ℂ_[p])} (H : Hyps l ex ph S) {ι : Type}
    {a : MvPowerSeries σ ℂ_[p]} (ha : Good a) (s : Finset ι) (e : ι → ℂ_[p])
    (he : ∀ i ∈ s, Good (mulBy l ex (e i) a)) : Good (mulBy l ex (∑ i ∈ s, e i) a) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, mulBy_zero H.data]
    exact good_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, mulBy_add H.data ha.1]
    exact hGA p l ex ph S H σ _ _ (he i (Finset.mem_insert_self i s))
      (ih (fun j hj => he j (Finset.mem_insert_of_mem hj)))
end PI.UnitaryGroupMassFormula.PhGram.ExpandW

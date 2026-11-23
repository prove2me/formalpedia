-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.goodAdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:54:17.124787+00:00
-- url     : https://prove2.me/submissions/dd03a616-cc36-40fb-a349-dc40d6e6ae15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_cc_add
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_PhGram_subst_add__9765ee5b53ae
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_cc_X
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_hasSubst_good
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_PhGram_integral_subst__38f52d75ab58


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
theorem _root_.solution : GoodAdd := by
  intro p _ l ex ph S H σ a b ha hb
  have hsG : ∀ i, Good (![a, b] i) := by
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
  have hs := hasSubst_good hsG
  have hI := integral_subst' ![a, b] hsG H.intAdd
  rw [subst_add' H.data hs (cc_X 0) (cc_X 1)] at hI
  have e0 : MvPowerSeries.subst ![a, b] (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = a :=
    MvPowerSeries.subst_X hs 0
  have e1 : MvPowerSeries.subst ![a, b] (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = b :=
    MvPowerSeries.subst_X hs 1
  rw [e0, e1] at hI
  exact ⟨cc_add H.data ha.1 hb.1, hI⟩
end PI.UnitaryGroupMassFormula.PhGram

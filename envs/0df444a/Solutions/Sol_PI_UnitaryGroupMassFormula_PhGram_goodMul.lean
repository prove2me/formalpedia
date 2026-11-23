-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.goodMul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:54:36.113575+00:00
-- url     : https://prove2.me/submissions/461a4d92-babe-4713-9c60-b446f8225e48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_cc_mulBy
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_subst_mulBy
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
theorem _root_.solution : GoodMul := by
  intro p _ l ex ph S H σ α hα a ha
  have hsG : ∀ i : Unit, Good ((fun _ : Unit => a) i) := fun _ => ha
  have hs := hasSubst_good hsG
  have hI := integral_subst' (fun _ : Unit => a) hsG (H.intMul α hα)
  rw [subst_mulBy H.data hs α.1 (cc_X ())] at hI
  have e : MvPowerSeries.subst (fun _ : Unit => a) (Xv () : MvPowerSeries Unit ℂ_[p]) = a :=
    MvPowerSeries.subst_X hs ()
  rw [e] at hI
  exact ⟨cc_mulBy H.data α.1 ha.1, hI⟩
end PI.UnitaryGroupMassFormula.PhGram

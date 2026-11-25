-- Prove2me | solution 1 for PI.AddIntG.Wk.zwEquation_thirdRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:12:03.885796+00:00
-- url     : https://prove2.me/submissions/3adb1a8f-7246-4cd7-9392-cf1c750c261b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_vieta1
import Theorems.Thm_PI_AddIntG_Wk_vieta2
import Theorems.Thm_PI_AddIntG_Wk_vieta3
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Classical
namespace PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
section order
variable {σ : Type*}
end order
private theorem chordCubic_var_zero_lemma (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (u : MvPowerSeries (Fin 2) ℂ_[p]) :
    G W u (lam wq * u + nu wq) = Acf W wq * u ^ 3 + Bcf W wq * u ^ 2 + Ccf W wq * u + Dcf W wq := by
  unfold G Acf Bcf Ccf Dcf
  ring
end PI.AddIntG.Wk
end
end

set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    G W (Z3 W wq) (lam wq * Z3 W wq + nu wq) = 0 := by
  rw [chordCubic_var_zero_lemma]
  linear_combination Z3 W wq ^ 2 * vieta1 W wq + Z3 W wq * vieta2 h + vieta3 h
end PI.AddIntG.Wk

-- Prove2me | solution 1 for PI.AddIntG.Wk.chordCubic_var_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:40:40.217019+00:00
-- url     : https://prove2.me/submissions/a833cfe8-6146-47e6-ac0f-9895ef62b1ed

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_G_wv
import Theorems.Thm_PI_AddIntG_Wk_lam_mul

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
    Acf W wq * Xv 1 ^ 3 + Bcf W wq * Xv 1 ^ 2 + Ccf W wq * Xv 1 + Dcf W wq = 0 := by
  have hw : wv wq 1 = lam wq * Xv 1 + nu wq := by
    unfold nu
    linear_combination (-1 : MvPowerSeries (Fin 2) ℂ_[p]) * lam_mul wq
  rw [← chordCubic_var_zero_lemma, ← hw]
  exact G_wv h 1
end PI.AddIntG.Wk

-- Prove2me | solution 1 for PI.AddIntG.Wk.chordCubic_var_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:41.429868+00:00
-- url     : https://prove2.me/submissions/3733c63c-d685-4495-b753-e45fb7acb937

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_G_wv

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
    Acf W wq * Xv 0 ^ 3 + Bcf W wq * Xv 0 ^ 2 + Ccf W wq * Xv 0 + Dcf W wq = 0 := by
  have hw : wv wq 0 = lam wq * Xv 0 + nu wq := by
    unfold nu
    ring
  rw [← chordCubic_var_zero_lemma, ← hw]
  exact G_wv h 0
end PI.AddIntG.Wk

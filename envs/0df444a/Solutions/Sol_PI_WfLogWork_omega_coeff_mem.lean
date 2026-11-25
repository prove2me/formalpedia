-- Prove2me | solution 1 for PI.WfLogWork.omega_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:38:19.632884+00:00
-- url     : https://prove2.me/submissions/04ab7913-0d56-4928-9413-4d29a03271af

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_CoefWfIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_FormalLogarithmHolds
import Theorems.Thm_PI_WfLogWork_mem_SerS_iff
import Theorems.Thm_PI_WfLogWork_Gv_memS
import Theorems.Thm_PI_WfLogWork_omega_eq
import Theorems.Thm_PI_AddIntG_Wk_inv_mem_SerS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WfLogWork
open PI.ExpIntWProof PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.WfLogWork
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ Wp p) (h2 : W.a₂ ∈ Wp p) (h3 : W.a₃ ∈ Wp p) (h4 : W.a₄ ∈ Wp p) (h6 : W.a₆ ∈ Wp p)
    (hW : AddIntG.IsWq W wq) (n : ℕ) : PowerSeries.coeff n (AddIntG.omegaW W wq) ∈ Wp p := by
  have hG := Gv_memS h1 h2 h3 h4 h6 hW
  have hc : PowerSeries.constantCoeff (-Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq)) = 1 := by
    simp [Gv, wser]
  have hinv := inv_mem_SerS (Wp p)
    (f := ((-Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq) : PowerSeries ℂ_[p]) :
      MvPowerSeries Unit ℂ_[p])) hc (neg_mem hG)
  rw [omega_eq hW]
  exact (mem_SerS_iff (Wp p) _).1 hinv n
end PI.WfLogWork

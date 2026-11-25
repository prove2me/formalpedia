-- Prove2me | solution 1 for PI.WfLogWork.Gv_memS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:28:08.170363+00:00
-- url     : https://prove2.me/submissions/e4a2b1b9-841b-4b40-8c5c-8936b0bd4616

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_CoefWfIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_FormalLogarithmHolds
import Theorems.Thm_PI_WfLogWork_mem_SerS_iff
import Theorems.Thm_PI_WfLogWork_C_memS
import Theorems.Thm_PI_WfLogWork_X_memS
import Theorems.Thm_PI_AddIntG_Wk_wq_mem


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
theorem _root_.solution {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (hW : AddIntG.IsWq W wq) :
    ((Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq) : PowerSeries ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) ∈
      SerS S Unit := by
  have hC : ∀ {a : ℂ_[p]}, a ∈ S →
      ((algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a : PowerSeries ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) ∈
        SerS S Unit := fun ha => C_memS ha
  have hX := X_memS (p := p) S
  have hw : (wq : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit :=
    (mem_SerS_iff S wq).2 (wq_mem h1 h2 h3 h4 h6 hW)
  have h2m : (2 : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by
    simpa using natCast_mem (SerS S Unit) 2
  have h3m : (3 : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by
    simpa using natCast_mem (SerS S Unit) 3
  have hv := mul_mem (pow_mem hX 3) hw
  simp only [Gv, wser]
  exact sub_mem (add_mem (add_mem (add_mem (add_mem (mul_mem (hC h1) hX)
    (mul_mem (hC h2) (pow_mem hX 2))) (mul_mem (mul_mem h2m (hC h3)) hv))
    (mul_mem (mul_mem (mul_mem h2m (hC h4)) hX) hv))
    (mul_mem (mul_mem h3m (hC h6)) (pow_mem hv 2))) (one_mem _)
end PI.WfLogWork

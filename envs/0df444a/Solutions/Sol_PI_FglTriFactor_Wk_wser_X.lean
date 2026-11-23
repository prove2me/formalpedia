-- Prove2me | solution 1 for PI.FglTriFactor.Wk.wser_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:26.5088+00:00
-- url     : https://prove2.me/submissions/72fa1a0b-cf5d-46a1-868e-6de2740379d4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglTriFactor PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglTriFactor.Wk
theorem _root_.solution {τ : Type*} (wq : PowerSeries ℂ_[p]) (i : τ) :
    PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries τ ℂ_[p]) (wser wq) =
      (MvPowerSeries.X i) ^ 3 * PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries τ ℂ_[p]) wq := by
  have hX := PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X (R := ℂ_[p]) i)
  rw [wser, PowerSeries.subst_mul hX, PowerSeries.subst_pow hX, PowerSeries.subst_X hX]
end PI.FglTriFactor.Wk

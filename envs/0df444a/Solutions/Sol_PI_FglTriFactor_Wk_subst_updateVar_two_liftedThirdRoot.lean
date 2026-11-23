-- Prove2me | solution 1 for PI.FglTriFactor.Wk.subst_updateVar_two_liftedThirdRoot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:26.188798+00:00
-- url     : https://prove2.me/submissions/93644cf8-d8fc-48e3-b352-187b03088c0a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
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
theorem _root_.solution (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) (t : MvPowerSeries (Fin 3) ℂ_[p])
    (ht : MvPowerSeries.constantCoeff t = 0) : MvPowerSeries.subst (upd 2 t) (s3 W wq) = s3 W wq := by
  have hz3 : ∀ i, MvPowerSeries.constantCoeff (upd 2 t i) = 0 := fun i => by
    fin_cases i <;> simp [upd, Function.update, ht]
  have hu : MvPowerSeries.HasSubst (upd 2 t) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hz3
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by rw [hz3 i]; exact IsNilpotent.zero)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hz3
  have hz2 : ∀ i, MvPowerSeries.constantCoeff
      (![MvPowerSeries.X 0, MvPowerSeries.X 1] i : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := fun i => by
    fin_cases i <;> simp
  have h2 : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]), MvPowerSeries.X 1] := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hz2
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by rw [hz2 i]; exact IsNilpotent.zero)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hz2
  unfold s3 pr
  rw [MvPowerSeries.subst_comp_subst_apply h2 hu]
  congr 1
  funext i
  fin_cases i
  · show MvPowerSeries.subst (upd 2 t) (MvPowerSeries.X 0) = MvPowerSeries.X 0
    rw [MvPowerSeries.subst_X hu]
    simp [upd, Function.update_apply]
  · show MvPowerSeries.subst (upd 2 t) (MvPowerSeries.X 1) = MvPowerSeries.X 1
    rw [MvPowerSeries.subst_X hu]
    simp [upd, Function.update_apply]
end PI.FglTriFactor.Wk

-- Prove2me | solution 1 for PI.WfEndProof.wfEnd_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:53.516641+00:00
-- url     : https://prove2.me/submissions/79301c3d-5e42-4722-a137-57ef564e01e4

import Definitions.Def_Formalism_PeriodIntegrals_W2pair
import Definitions.Def_Formalism_PeriodIntegrals_WfRing
import Definitions.Def_Formalism_PeriodIntegrals_WfSubst
import Definitions.Def_Formalism_PeriodIntegrals_InvSerSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_StepIII
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittEndomorphism_FlogConstantCoeff
import Theorems.Thm_P2M_PI_WfEndProof_flog_constantCoeff__e5fd9c502ec2
import Theorems.Thm_PI_WfEndProof_coefWf_X
import Theorems.Thm_PI_ExpIntWProof_keyW
import Theorems.Thm_PI_ExpIntWProof_stepIII_of_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WfEndProof
open PI
namespace PI.WfEndProof
theorem _root_.solution (hR : WfRing) (hS : WfSubst) (hL : WfLog) : WfEnd := by
  intro p _ W wq ex h1 h2 h3 h4 h6 hW hex hsub c hc hI n
  obtain ⟨hl, hx⟩ := hL p W wq ex h1 h2 h3 h4 h6 hW hex hsub
  have hX : CoefWf (MvPowerSeries.X () : MvPowerSeries Unit ℂ_[p]) := coefWf_X p
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X () : MvPowerSeries Unit ℂ_[p]) = 0 := by simp
  have hA := hS p Unit (AddIntG.flog W wq) (MvPowerSeries.X ()) hl hX hX0
  have hB := (hR p Unit _ _ hA hA).2.2.2 c hc
  have hB0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c *
      PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit ℂ_[p]) (AddIntG.flog W wq)) = 0 := by
    rw [map_mul, PowerSeries.constantCoeff_subst_eq_zero hX0 _ (flog_constantCoeff' W wq), mul_zero]
  have hM := hS p Unit ex _ hx hB hB0
  exact PI.ExpIntWProof.stepIII_of_key PI.ExpIntWProof.keyW p _ (hM n) (hI n)
end PI.WfEndProof

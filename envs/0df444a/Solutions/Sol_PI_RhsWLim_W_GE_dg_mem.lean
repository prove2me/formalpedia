-- Prove2me | solution 1 for PI.RhsWLim.W.GE.dg_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:37.703956+00:00
-- url     : https://prove2.me/submissions/dd1bf910-7792-488b-b1ab-ccb879a879c6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ChartLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_GaugeExists
import Theorems.Thm_PI_RhsWLim_W_GE_firstMiddle_val
import Theorems.Thm_PI_RhsWLim_W_GE_dg_uh
import Theorems.Thm_PI_RhsWLim_W_GE_dg_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
open PI.RhsWLim.W.GE
variable {k r : ℕ}
namespace PI.RhsWLim.W.GE
theorem _root_.solution (u : ℂ) (hu : star u * u = 1) : dg k r u ∈ UWb k r := by
  show dg k r u ∈ UH (Hpk k r) ∧ ∀ a : Fin r, dg k r u *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
    dg k r u *ᵥ bvec (esI k r a) = bvec (esI k r a)
  have hv := firstMiddle_val (k := k) (r := r)
  refine ⟨dg_uh u hu, fun a => ⟨dg_fix u _ ?_, dg_fix u _ ?_⟩⟩
  · intro h
    have h1 : (eI k r a).val = (p0 k r).val := congrArg Fin.val h
    have h2 : (eI k r a).val = a.val := rfl
    have h3 := a.isLt
    omega
  · intro h
    have h1 : (esI k r a).val = (p0 k r).val := congrArg Fin.val h
    have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
    have h3 := a.isLt
    omega
end PI.RhsWLim.W.GE

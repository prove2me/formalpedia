-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.Sd.continuous_psiV_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:52.302469+00:00
-- url     : https://prove2.me/submissions/a0aa9322-a983-4a0e-a613-4eba55ab2cec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousTrESymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousPsiVOf
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_psiV_add__9a67760e36c5
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_ballK_mem_nhds
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_psiV_ballK
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp.Sd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable (ψ : AddChar (AF F) ℂ)
namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd
theorem _root_.solution (h : OpenKer v ψ) : Continuous (psiV F ψ v) := by
  obtain ⟨k, hk⟩ := h
  refine continuous_iff_continuousAt.2 fun r => ?_
  have hev : ∀ᶠ t in 𝓝 r, psiV F ψ v t = psiV F ψ v r := by
    have h1 : Tendsto (fun t => t - r) (𝓝 r) (𝓝 0) := tendsto_sub_nhds_zero_iff.2 tendsto_id
    filter_upwards [h1 (ballK_mem_nhds v k)] with t ht
    have := psiV_add' v ψ r (t - r)
    rw [add_sub_cancel, psiV_ballK v ψ hk ht, mul_one] at this
    exact this
  exact continuousAt_const.congr (hev.mono fun t ht => ht.symm)
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd

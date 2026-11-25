-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.Sd.ballK_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:53.434035+00:00
-- url     : https://prove2.me/submissions/71349a75-bb86-4ea7-9a57-bab5498b2f8c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousTrESymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousPsiVOf
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
theorem _root_.solution (k : ℕ) : ballK v k ∈ 𝓝 (0 : Fv F v) := by
  have ho : IsOpen (ballK v k) :=
    (Valued.isOpen_valuationSubring _).preimage (continuous_const.mul continuous_id)
  exact ho.mem_nhds (by simp [ballK, zero_mem])
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd

-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.Sd.psiV_neg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:37:04.195817+00:00
-- url     : https://prove2.me/submissions/83f530e9-62f9-4f26-a40c-26a1a971ebcf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousTrESymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousPsiVOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_psiV_zero
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_psiV_add__9a67760e36c5
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
theorem _root_.solution (r : Fv F v) : psiV F ψ v (-r) * psiV F ψ v r = 1 := by
  rw [← psiV_add', neg_add_cancel, psiV_zero]
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd

-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.Sd.psiV_ballK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:30.187301+00:00
-- url     : https://prove2.me/submissions/3e7c38e3-ef07-4b85-a80c-1ab9a90b8095

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousTrESymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousPsiVOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_piu_ne
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
theorem _root_.solution {k : ℕ} (hk : ∀ c ∈ v.adicCompletionIntegers F, psiV F ψ v (piu v ^ k * c) = 1)
    {t : Fv F v} (ht : t ∈ ballK v k) : psiV F ψ v t = 1 := by
  have h := hk _ ht
  rwa [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero k (piu_ne v)), one_mul] at h
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd

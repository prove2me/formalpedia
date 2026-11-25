-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.Sd.openKer_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:17.01795+00:00
-- url     : https://prove2.me/submissions/ac9be38f-aeb2-4de7-8ce2-1e6f8c4bf551

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousTrESymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousPsiVOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_tube
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
theorem _root_.solution (t : Fv F v) (ht : t ≠ 0)
    (h : ∀ c ∈ v.adicCompletionIntegers F, psiV F ψ v (c * t) = 1) : OpenKer v ψ := by
  have hU : {s : Fv F v | t⁻¹ * s ∈ v.adicCompletionIntegers F} ∈ 𝓝 (0 : Fv F v) :=
    ((Valued.isOpen_valuationSubring _).preimage (continuous_const.mul continuous_id)).mem_nhds
      (by simp [zero_mem])
  obtain ⟨k, hk⟩ := (tube v (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v) hU).exists
  refine ⟨k, fun c hc => ?_⟩
  have h1 := h _ (hk c hc)
  simp only [smul_eq_mul] at h1
  have e : t⁻¹ * (piu v ^ k * c) * t = piu v ^ k * c := by field_simp
  rwa [e] at h1
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd

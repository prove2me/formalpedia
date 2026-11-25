-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.Sd.tube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:24:46.502535+00:00
-- url     : https://prove2.me/submissions/e8b83f33-b2cb-46f7-9cde-34f44a5b186b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousTrESymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ContinuousPsiVOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_Sd_piu_tendsto
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
namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd
theorem _root_.solution {X : Type} [AddCommGroup X] [Module (Fv F v) X] [TopologicalSpace X]
    [ContinuousSMul (Fv F v) X] {C : Set X} (hC : IsCompact C) {U : Set X}
    (hU : U ∈ 𝓝 (0 : X)) : ∀ᶠ k : ℕ in atTop, ∀ c ∈ C, piu v ^ k • c ∈ U := by
  have hP : ∀ c ∈ C, ∀ᶠ z : Fv F v × X in 𝓝 ((0 : Fv F v), c), z.1 • z.2 ∈ U := by
    intro c _
    have hc : Continuous fun z : Fv F v × X => z.1 • z.2 := continuous_fst.smul continuous_snd
    exact (hc.tendsto ((0 : Fv F v), c)).eventually_mem (by simpa using hU)
  have hev := hC.eventually_forall_of_forall_eventually (P := fun s c => s • c ∈ U) hP
  exact (piu_tendsto v).eventually hev
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd

-- Prove2me | solution 1 for PI.OmFibreUniq.W.Sd.sdEx_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:16:05.207901+00:00
-- url     : https://prove2.me/submissions/44e50772-5060-48ee-bbbe-081bb0c375f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DetAdmA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SmulMemHermR
import Theorems.Thm_PI_VolStabSW_SdUniqW_continuous_psiV
import Theorems.Thm_PI_VolStabSW_SdUniqW_psiV_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.Sd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.VolStabSW PI.VolStabSW.SdUniqW PI.AdicCompletionValuation
open scoped TensorProduct
namespace PI.OmFibreUniq.W.Sd
theorem _root_.solution (hP : PsiNT) (hA : AbsSd) (hWf : BRFacts) (hW : FrameW) (hHf : HermFacts)
    (hH : FrameH) : SdEx := by
  intro F E _ _ _ _ _ σ n J ψ v a hS
  obtain ⟨hCM, hJ, hψ, hstd⟩ := hS
  have hc : Continuous (psiV F ψ v) := continuous_psiV ψ hψ.1 v
  have hadd := psiV_add ψ v
  have hn : ∀ r, ‖psiV F ψ v r‖ = 1 := fun r => hψ.2.1 _
  have hnt := hP ψ v hψ hstd hCM.1
  constructor
  · obtain ⟨ι, _, β, β', h1, h2⟩ := hW σ J v a hCM hJ
    obtain ⟨ha, hs, hsym, hcont⟩ := hWf σ J v a hCM hJ
    obtain ⟨μ, hμ⟩ := hA v _ hc hadd hn hnt (BR (Fv F v) σ J) ha hs hsym hcont β β' h1 h2
    exact ⟨μ, hμ⟩
  · obtain ⟨ι, _, β, β', h1, h2⟩ := hH σ v a hCM
    obtain ⟨ha, hs, hsym, hcont⟩ := hHf σ v a hCM
    obtain ⟨μ, hμ⟩ := hA v _ hc hadd hn hnt (pairHerm (Fv F v) σ a) ha hs hsym hcont β β' h1 h2
    exact ⟨μ, hμ⟩
end PI.OmFibreUniq.W.Sd

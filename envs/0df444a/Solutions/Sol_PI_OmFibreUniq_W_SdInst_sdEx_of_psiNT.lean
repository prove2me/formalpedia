-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdInst.sdEx_of_psiNT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:10.20694+00:00
-- url     : https://prove2.me/submissions/62e01be8-dc6f-4432-bd1e-c4de0cab0212

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExInst
import Theorems.Thm_PI_OmFibreUniq_W_SdInst_BR_symm
import Theorems.Thm_PI_OmFibreUniq_W_SdInst_BR_cont_joint
import Theorems.Thm_PI_OmFibreUniq_W_SdInst_pairHerm_symm
import Theorems.Thm_PI_OmFibreUniq_W_SdInst_pairHerm_smul
import Theorems.Thm_PI_OmFibreUniq_W_SdInst_pairHerm_cont_joint
import Theorems.Thm_PI_OmFibreUniq_W_SdAbs_exists_selfDual_measure
import Theorems.Thm_PI_VolStabSW_SdDualW_dualAt_H
import Theorems.Thm_PI_VolStabSW_SdDualW_dualAt_alt
import Theorems.Thm_PI_VolStabSW_SdDualW_nondeg_BR
import Theorems.Thm_PI_VolStabSW_SdUniqW_BR_add
import Theorems.Thm_PI_VolStabSW_SdUniqW_continuous_psiV
import Theorems.Thm_PI_VolStabSW_SdUniqW_pairHerm_add
import Theorems.Thm_PI_VolStabSW_SdUniqW_psiV_add
import Theorems.Thm_PI_VolStabSW_sigma_invol


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdInst
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.Sd PI.OmFibreUniq.W.SdAbs
open PI.VolStabSW PI.VolStabSW.SdUniqW PI.VolStabSW.SdDualW PI.AdicCompletionValuation
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.OmFibreUniq.W.SdInst
theorem _root_.solution (hP : PsiNT) : SdEx := by
  intro F E _ _ _ _ _ σ n J ψ v a hS
  obtain ⟨hCM, hJ, hψ, hstd⟩ := hS
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have hc : Continuous (psiV F ψ v) := continuous_psiV ψ hψ.1 v
  have hadd := psiV_add ψ v
  have hn : ∀ r, ‖psiV F ψ v r‖ = 1 := fun r => hψ.2.1 _
  have hnt := hP ψ v hψ hstd hCM.1
  constructor
  · obtain ⟨μ, hμ⟩ := exists_selfDual_measure v (BR (Fv F v) σ J (n := a)) (psiV F ψ v) hc hadd hn hnt
      (fun x x' y => BR_add (Fv F v) σ J x' x y) (fun c x y => BR_smul_left v σ J c x y)
      (BR_symm v σ hσ J hJ.1) (BR_cont_joint v σ J)
      (dualAt_alt v (Module.finBasis F E) σ J (nondeg_BR v σ hσ J hJ.2))
    exact ⟨μ, hμ⟩
  · obtain ⟨μ, hμ⟩ := exists_selfDual_measure v (pairHerm (Fv F v) σ a) (psiV F ψ v) hc hadd hn hnt
      (fun x x' y => pairHerm_add (Fv F v) σ a x' x y) (fun c x y => pairHerm_smul v σ a c x y)
      (pairHerm_symm v σ a) (pairHerm_cont_joint v σ a)
      (dualAt_H v (Module.finBasis F E) σ hσ a)
    exact ⟨μ, hμ⟩
end PI.OmFibreUniq.W.SdInst

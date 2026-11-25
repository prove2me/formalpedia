-- Prove2me | solution 1 for PI.VolStabW.sdTestInf_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:39.797795+00:00
-- url     : https://prove2.me/submissions/bcbdddbd-4415-46b4-8e7c-1eb5ddc52712

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RealCharacter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdTestInf
import Theorems.Thm_P2M_PI_VolStabW_SdTestInfW_BR_add_right__4f8a28ccbc2c
import Theorems.Thm_P2M_PI_VolStabW_SdTestInfW_pairHerm_add_right__b5dc66635d8a
import Theorems.Thm_PI_VolStabW_SdTestInfW_continuous_BR_left
import Theorems.Thm_PI_VolStabW_SdTestInfW_continuous_pairHerm_left
import Theorems.Thm_P2M_PI_VolStabW_SdTestInfW_continuous_psiInf__007137ef755b
import Theorems.Thm_PI_VolStabW_SdTestInfW_testEx_coord
import Theorems.Thm_PI_VolStabW_SdUniqW_BR_add
import Theorems.Thm_PI_VolStabW_SdUniqW_continuous_BR_right
import Theorems.Thm_PI_VolStabW_SdUniqW_continuous_pairHerm_right
import Theorems.Thm_PI_VolStabW_SdUniqW_pairHerm_add
import Theorems.Thm_PI_VolStabW_SdUniqW_psiInf_add
import Theorems.Thm_PI_VolStabW_tensR_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation PI.VolFromSW SdUniqW SdTestInfW
namespace PI.VolStabW
theorem _root_.solution : SdTestInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨n, m, eV, eH, hV, hH⟩ := tensR_holds F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet
  have : SecondCountableTopology (HermR (Ainf F) σ a) :=
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ainf F ⊗[F] E))
    Topology.IsInducing.subtypeVal.secondCountableTopology
  have hpc := continuous_psiInf' ψ hψ.1
  have hpn : ∀ r, ‖psiInf F ψ r‖ = 1 := fun r => hψ.2.1 _
  refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
  · have := hμ.1
    exact testEx_coord μ _ eV hV (fun X X' Y => by rw [BR_add, psiInf_add])
      (fun X Y Y' => by rw [BR_add_right', psiInf_add]) (fun X Y => hpn _)
      (fun Y => hpc.comp (continuous_BR_left (Ainf F) σ J Y))
      (fun X => hpc.comp (continuous_BR_right (Ainf F) σ J X))
  · have := hν.1
    exact testEx_coord ν _ eH hH (fun S S' T => by rw [pairHerm_add, psiInf_add])
      (fun S T T' => by rw [pairHerm_add_right', psiInf_add]) (fun S T => hpn _)
      (fun T => hpc.comp (continuous_pairHerm_left (Ainf F) σ a T))
      (fun S => hpc.comp (continuous_pairHerm_right (Ainf F) σ a S))
end PI.VolStabW

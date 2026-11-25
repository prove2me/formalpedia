-- Prove2me | solution 1 for PI.VolStabW.sdUniq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:50:26.414666+00:00
-- url     : https://prove2.me/submissions/777a3bc7-7190-4eb5-813f-d36bd8817222

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Theorems.Thm_PI_VolStabW_SdUniqW_eq_of_testEx
import Theorems.Thm_PI_VolStabW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabW_secondCountable_Fv


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
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW
namespace PI.VolStabW
theorem _root_.solution (hI : SdTestInf) (hV : SdTestV) : SdUniq := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨hIW, hIH⟩ := hI F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ
  have : SecondCountableTopology (HermR (Ainf F) σ a) :=
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ainf F ⊗[F] E))
    Topology.IsInducing.subtypeVal.secondCountableTopology
  refine ⟨fun μ1 μ2 e1 e2 => eq_of_testEx e1 e2 (hIW μ1 e1),
    fun ν1 ν2 e1 e2 => eq_of_testEx e1 e2 (hIH ν1 e1), fun v => ?_⟩
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  obtain ⟨hVW, hVH⟩ := hV F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ v
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
    Topology.IsInducing.subtypeVal.secondCountableTopology
  exact ⟨fun μ1 μ2 e1 e2 => eq_of_testEx e1 e2 (hVW μ1 e1),
    fun ν1 ν2 e1 e2 => eq_of_testEx e1 e2 (hVH ν1 e1)⟩
end PI.VolStabW

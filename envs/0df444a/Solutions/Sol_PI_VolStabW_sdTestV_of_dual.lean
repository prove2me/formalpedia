-- Prove2me | solution 1 for PI.VolStabW.sdTestV_of_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:49:42.209923+00:00
-- url     : https://prove2.me/submissions/4b7f2c1e-020e-4f44-ba5b-bb56b2f03882

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Theorems.Thm_PI_VolStabW_SdUniqW_testEx_of_lattice
import Theorems.Thm_PI_VolStabW_SdUniqW_testEx_of_trivial
import Theorems.Thm_PI_VolStabW_SdUniqW_annAt_of_dual
import Theorems.Thm_PI_VolStabW_SdUniqW_psiV_add
import Theorems.Thm_PI_VolStabW_SdUniqW_continuous_psiV
import Theorems.Thm_PI_VolStabW_SdUniqW_BR_add
import Theorems.Thm_PI_VolStabW_SdUniqW_pairHerm_add
import Theorems.Thm_PI_VolStabW_SdUniqW_continuous_BR_right
import Theorems.Thm_PI_VolStabW_SdUniqW_continuous_pairHerm_right
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
theorem _root_.solution (h : DualLatV) : SdTestV := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  obtain ⟨hDW, hDH⟩ := h F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v
  by_cases hψv : ∃ r, psiV F ψ v r ≠ 1
  · obtain ⟨r0, h0⟩ := hψv
    have hc := continuous_psiV ψ hψ.1 v
    obtain ⟨L, hLc, hLo, hA, K, hK, hAK⟩ :=
      annAt_of_dual v _ _ hc (fun X => continuous_BR_right (Fv F v) σ J X) r0 h0 hDW
    obtain ⟨L', hLc', hLo', hA', K', hK', hAK'⟩ :=
      annAt_of_dual v _ _ hc (fun S => continuous_pairHerm_right (Fv F v) σ a S) r0 h0 hDH
    refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
    · have := hμ.1
      exact testEx_of_lattice μ _ (fun X T Y => by rw [BR_add, psiV_add]) L hLc hLo
        hA K hK hAK
    · have := hν.1
      exact testEx_of_lattice ν _ (fun S T U => by rw [pairHerm_add, psiV_add]) L'
        hLc' hLo' hA' K' hK' hAK'
  · simp only [not_exists, not_not] at hψv
    obtain ⟨L, hLc, hLo, -⟩ := hDW
    obtain ⟨L', hLc', hLo', -⟩ := hDH
    refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
    · have := hμ.1
      exact testEx_of_trivial μ _ (fun _ _ => hψv _) L hLc hLo
    · have := hν.1
      exact testEx_of_trivial ν _ (fun _ _ => hψv _) L' hLc' hLo'
end PI.VolStabW

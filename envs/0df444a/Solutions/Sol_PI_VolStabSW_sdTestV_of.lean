-- Prove2me | solution 1 for PI.VolStabSW.sdTestV_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:32:26.305619+00:00
-- url     : https://prove2.me/submissions/8326c00e-fdfa-430f-9738-1738f7ea3c4e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Theorems.Thm_PI_VolStabSW_SdUniqW_testEx_of_lattice
import Theorems.Thm_PI_VolStabSW_SdUniqW_psiV_add
import Theorems.Thm_PI_VolStabSW_SdUniqW_BR_add
import Theorems.Thm_PI_VolStabSW_SdUniqW_pairHerm_add
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
open PI PI.VolStabSW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW
namespace PI.VolStabSW
theorem _root_.solution (h : AnnV) : SdTestV := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  obtain ⟨⟨L, hLc, hLo, hA, K, hK, hAK⟩, ⟨L', hLc', hLo', hA', K', hK', hAK'⟩⟩ :=
    h F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ v
  refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
  · have := hμ.1
    exact testEx_of_lattice μ _ (fun X T Y => by rw [BR_add, psiV_add]) L hLc hLo hA K
      hK hAK
  · have := hν.1
    exact testEx_of_lattice ν _ (fun S T U => by rw [pairHerm_add, psiV_add]) L' hLc'
      hLo' hA' K' hK' hAK'
end PI.VolStabSW

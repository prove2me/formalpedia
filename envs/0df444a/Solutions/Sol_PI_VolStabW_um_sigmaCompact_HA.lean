-- Prove2me | solution 1 for PI.VolStabW.um_sigmaCompact_HA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:42:20.340442+00:00
-- url     : https://prove2.me/submissions/01531777-e21e-49ec-8cd1-b75b75ab1aea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_Unimod
import Theorems.Thm_PI_VolStabW_um_sigmaCompact
import Theorems.Thm_PI_VolStabW_um_countable_HFinIn

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
open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.AdicCompletionValuation NumberField
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (h : SWa1 F E σ M J) : SigmaCompactSpace (HA (AF F) σ J) := by
  obtain ⟨μ, hμ⟩ := h.1
  have : μ.IsHaarMeasure := hμ
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := um_countable_HFinIn F E σ M J
  obtain ⟨𝓕, h𝓕⟩ := (h.2 μ hμ).1
  exact um_sigmaCompact Γ μ 𝓕 h𝓕 ((h.2 μ hμ).2 𝓕 h𝓕)
end PI.VolStabW

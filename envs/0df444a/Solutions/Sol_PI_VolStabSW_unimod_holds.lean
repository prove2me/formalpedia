-- Prove2me | solution 1 for PI.VolStabSW.unimod_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:21:18.049098+00:00
-- url     : https://prove2.me/submissions/64c2d101-2bf7-4c1d-b2b5-7b2d335260b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_Unimod
import Theorems.Thm_PI_VolStabSW_um_rightInv
import Theorems.Thm_PI_VolStabSW_um_countable_HFinIn

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
open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.AdicCompletionValuation NumberField
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution : Unimod := by
  intro F E _ _ _ _ _ σ hσ M J _ hSWa1 _ _ _ _ _ _ _ μ hμ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have : μ.IsHaarMeasure := hμ
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := um_countable_HFinIn F E σ M J
  obtain ⟨𝓕, h𝓕⟩ := (hSWa1.2 μ hμ).1
  exact um_rightInv Γ μ 𝓕 h𝓕 ((hSWa1.2 μ hμ).2 𝓕 h𝓕)
end PI.VolStabSW

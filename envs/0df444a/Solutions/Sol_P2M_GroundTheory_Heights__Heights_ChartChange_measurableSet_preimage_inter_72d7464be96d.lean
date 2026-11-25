-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartChange_measurableSet_preimage_inter_72d7464be96d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:41.927814+00:00
-- url     : https://prove2.me/submissions/a24f1ba4-a812-49b3-ba88-b908f3f62ecd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntChartChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeSheetNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntChartChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.ChartChange
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartChange
theorem _root_.solution {Ψ : (Fin n → ℂ) → Fin n → ℂ} {U S E : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hΨ : ContinuousOn Ψ U) (hSU : S ⊆ U) (hS : MeasurableSet S)
    (hE : MeasurableSet E) : MeasurableSet (Ψ ⁻¹' E ∩ S) := by
  classical
  have hm : Measurable (U.piecewise Ψ fun _ => 0) :=
    hΨ.measurable_piecewise continuousOn_const hU.measurableSet
  have : Ψ ⁻¹' E ∩ S = (U.piecewise Ψ fun _ => 0) ⁻¹' E ∩ S := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [Set.piecewise_eq_of_mem _ _ _ (hSU h2)], h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [Set.piecewise_eq_of_mem _ _ _ (hSU h2)] at h1, h2⟩
  rw [this]
  exact (hm hE).inter hS
end GroundTheory.Heights₂.Heights.ChartChange

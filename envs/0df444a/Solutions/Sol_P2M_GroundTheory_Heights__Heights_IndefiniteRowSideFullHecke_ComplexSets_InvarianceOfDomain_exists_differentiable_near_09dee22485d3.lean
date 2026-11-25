-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_exists_differentiable_near_09dee22485d3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:06:08.799781+00:00
-- url     : https://prove2.me/submissions/696606b0-b215-4820-8165-afc1b4048474
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInvarianceOfDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBrouwerFixedPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInvarianceOfDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_smoothSubalgebra_separatesPoints_dc2671d39c14

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
open Metric Set MeasureTheory
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
theorem _root_.solution {S : Set (Fin n → ℝ)} (hS : IsCompact S)
    (G : (Fin n → ℝ) → Fin n → ℝ) (hG : Continuous G) {η : ℝ} (hη : 0 < η) :
    ∃ P : (Fin n → ℝ) → Fin n → ℝ, Differentiable ℝ P ∧ ∀ y ∈ S, ‖P y - G y‖ < η := by
  have h : ∀ i : Fin n, ∃ g ∈ smoothSubalgebra n, ∀ y ∈ S, ‖(g : (Fin n → ℝ) → ℝ) y - G y i‖ < η :=
    fun i => ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      smoothSubalgebra_separatesPoints ⟨fun y => G y i, (continuous_apply i).comp hG⟩ hS hη
  choose g hg hgS using h
  refine ⟨fun y i => g i y, differentiable_pi.2 fun i => ?_, fun y hy => ?_⟩
  · exact (show ContDiff ℝ 1 (g i : (Fin n → ℝ) → ℝ) from hg i).differentiable one_ne_zero
  · rw [pi_norm_lt_iff hη]
    intro i
    simpa using hgS i y hy
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain

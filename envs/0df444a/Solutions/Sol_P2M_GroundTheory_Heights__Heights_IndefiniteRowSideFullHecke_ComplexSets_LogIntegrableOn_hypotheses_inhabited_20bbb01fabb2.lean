-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_LogIntegrableOn_hypotheses_inhabited_20bbb01fabb2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:58:31.333133+00:00
-- url     : https://prove2.me/submissions/c20792c9-06cb-47e7-85fb-97f46e8f65a1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_contDiff_normSq_coord_a499efa3db51
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isAffVariety_bot_ca242a8c4e80
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isFiniteProj_one_a3712cd17b90
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smoothNear_of_contDiff_4853c0abca34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_one_not_mem_point_805b757dbb4c


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
open MvPolynomial MeasureTheory
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace LogIntegrableOn
theorem _root_.solution :
    IsAffVariety (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1 ∧
      IsFiniteProj (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) ∧
      (∀ i : Fin 1, SmoothNear (zeroLocus (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)))
        ((fun _ x => ‖x 0‖ ^ 2 : Fin 1 → (Fin 1 → ℂ) → ℝ) i)) ∧
      linForm (fun _ : Fin 1 => (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      MeasurableSet (Metric.ball (0 : Fin 1 → ℂ) 1) ∧
      Bornology.IsBounded (Metric.ball (0 : Fin 1 → ℂ) 1) :=
  ⟨isAffVariety_bot 1, isFiniteProj_one 1, fun _ => smoothNear_of_contDiff _ contDiff_normSq_coord,
    linForm_one_not_mem_point ℂ, measurableSet_ball, Metric.isBounded_ball⟩
end LogIntegrableOn
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

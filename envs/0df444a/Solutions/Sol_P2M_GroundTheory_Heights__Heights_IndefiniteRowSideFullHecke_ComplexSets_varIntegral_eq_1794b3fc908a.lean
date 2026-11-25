-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_varIntegral_eq_1794b3fc908a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:26:13.445015+00:00
-- url     : https://prove2.me/submissions/a3db52ac-b6b2-44d7-a826-1d31285557a0

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isFiniteProj_iff_2c15bda3c982
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_projInt_eq_c90a4342675f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_choose_congr_4ab2779346b4

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
open MvPolynomial MeasureTheory Filter Topology Matrix
noncomputable section
variable {n d : ℕ}
variable {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) (g : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (hJ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety J d) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.varIntegral J g φ =
      GroundTheory.Heights₂.Heights.varInt J d g φ := by
  have hp : (fun A : Matrix (Fin d) (Fin n) ℂ =>
        GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsFiniteProj J A) =
      fun A => GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A :=
    funext fun A => propext (isFiniteProj_iff hJ)
  unfold GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.varIntegral GroundTheory.Heights₂.Heights.varInt
  by_cases h : ∃ A : Matrix (Fin d) (Fin n) ℂ,
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A
  · have h' : ∃ A : Matrix (Fin d) (Fin n) ℂ,
        GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsFiniteProj J A := by
      obtain ⟨A, hA⟩ := h
      exact ⟨A, (isFiniteProj_iff hJ).mpr hA⟩
    rw [dif_pos h, dif_pos h', projInt_eq, choose_congr hp h' h]
  · have h' : ¬ ∃ A : Matrix (Fin d) (Fin n) ℂ,
        GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsFiniteProj J A := by
      rintro ⟨A, hA⟩
      exact h ⟨A, (isFiniteProj_iff hJ).mp hA⟩
    rw [dif_neg h, dif_neg h']
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

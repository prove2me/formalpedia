-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sheetDens_eq_d81652801c0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:36.600028+00:00
-- url     : https://prove2.me/submissions/ba697d97-9073-40a2-8c9e-492b2f7d2b71

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_graphChart_iff_1221eaf5508a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_maDens_graphChart_eq_sheet_4e944c13118d

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
open Classical
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (φ : Fin d → (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.sheetDens J A φ x =
      if h : ∃ s, GroundTheory.Heights₂.Heights.IsSheetAt J A x s then
        ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ x) else 0 := by
  unfold GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.sheetDens
  by_cases h : ∃ σ, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGraphChart J A x σ
  · have h' : ∃ s, GroundTheory.Heights₂.Heights.IsSheetAt J A x s := exists_graphChart_iff.mp h
    rw [dif_pos h, dif_pos h']
    exact maDens_graphChart_eq_sheet h.choose_spec h'.choose_spec φ
  · have h' : ¬ ∃ s, GroundTheory.Heights₂.Heights.IsSheetAt J A x s :=
      fun h' => h (exists_graphChart_iff.mpr h')
    rw [dif_neg h, dif_neg h']
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

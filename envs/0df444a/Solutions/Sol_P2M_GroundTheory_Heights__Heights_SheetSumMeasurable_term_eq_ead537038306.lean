-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_term_eq_ead537038306
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:48.301959+00:00
-- url     : https://prove2.me/submissions/c68f236b-ad2f-4d2a-ab5a-38993f3f440e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsSheetMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_sheet_eventuallyEq_f5b44630f2f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_maDens_congr_of_eventuallyEq_290b4083a720


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.SheetSumMeasurable
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.SheetSumMeasurable
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (Φ : ℝ → ℝ → ℝ) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) {x : Fin n → ℂ}
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) (h : ∃ s, IsSheetAt J A x s) :
    Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ x)) =
      Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (A *ᵥ x)) := by
  rw [IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k =>
    ((sheet_eventuallyEq hs h.choose_spec).fun_comp (φ k))]
end GroundTheory.Heights₂.Heights.SheetSumMeasurable

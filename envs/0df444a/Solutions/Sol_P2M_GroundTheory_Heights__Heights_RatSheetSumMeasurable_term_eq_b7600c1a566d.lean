-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_term_eq_b7600c1a566d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:36.896318+00:00
-- url     : https://prove2.me/submissions/f5941c3f-0bba-460a-9d4d-1147bdd08c29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetSumMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_sheet_eventuallyEq_1d9f0375eb0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_maDens_congr_of_eventuallyEq_290b4083a720
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_sheet_eventuallyEq_f5b44630f2f2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ComplexSets
open GroundTheory.Heights₂.Heights.RatSheetSumMeasurable
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.RatSheetSumMeasurable
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (Φ : ℝ → ℝ → ℝ) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : RatChart.IsRatSheetAt J p q x s)
    (h : ∃ s, RatChart.IsRatSheetAt J p q x s) :
    Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (RatChart.ratMap p q x)) =
      Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (RatChart.ratMap p q x)) := by
  rw [IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k =>
    ((sheet_eventuallyEq hs h.choose_spec).fun_comp (φ k))]
end GroundTheory.Heights₂.Heights.RatSheetSumMeasurable

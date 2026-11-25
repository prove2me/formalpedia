-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.sheet_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:58:24.320237+00:00
-- url     : https://prove2.me/submissions/0b860392-29e0-421f-a27e-5a98fbdfda2e

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeSheets
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Theorems.Thm_ReciprocityTheory_AnForm_M_degree_det_restrictScalars
import Theorems.Thm_ReciprocityTheory_AnForm_M_degree_sheet_chart_data
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensPullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (j : Fin B.n) (k : Fin A.n) {W : Set Y} {V : Set X} (hW : IsOpen W)
    (hWj : W ⊆ (B.chart j).source) (hVk : V ⊆ (A.chart k).source) (hbij : Set.BijOn h W V)
    (f : X → ENNReal) :
    ∫⁻ y in (B.chart j) '' W, f (h ((B.chart j).symm y)) *
        ENNReal.ofReal |locDens B (fun i => (Φ i).pullback h hh.1) j y| =
      ∫⁻ z in (A.chart k) '' V, f ((A.chart k).symm z) * ENNReal.ofReal |locDens A Φ k z| := by
  obtain ⟨hU, himg, hinj, hder, hsrc⟩ := degree_sheet_chart_data hh j k hW hWj hVk hbij
  set φ := A.chart k ∘ h ∘ (B.chart j).symm with hφ
  rw [← himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU hder hinj]
  refine setLIntegral_congr_fun hU fun y hy => ?_
  have hyT : y ∈ (B.chart j).target := by
    obtain ⟨w, hw, rfl⟩ := hy
    exact (B.chart j).map_source (hWj hw)
  simp only [hφ, degree_det_restrictScalars, Function.comp_apply,
    (A.chart k).left_inv (hsrc y hy)]
  rw [locDensPullback A B h hh Φ hΦ j k y hyT (hsrc y hy)]
  simp only [abs_mul, abs_pow, abs_norm]
  rw [ENNReal.ofReal_mul (abs_nonneg _)]
  ring
end ReciprocityTheory.AnForm.M

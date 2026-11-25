-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.locDensChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:06.959342+00:00
-- url     : https://prove2.me/submissions/2d4342da-928a-4a3c-8e34-2abdb6d674e0

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Theorems.Thm_ReciprocityTheory_AnForm_M_hessCGerm
import Theorems.Thm_ReciprocityTheory_AnForm_M_maDens_congr_hessC
import Theorems.Thm_ReciprocityTheory_AnForm_M_potSmoothAt
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_jacC
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff ComplexOrder Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : LocDensChartStatement := by
  intro e X _ A Φ hΦ j k y hy hyk
  have hback : (A.chart k).symm (A.chart k ((A.chart j).symm y)) = (A.chart j).symm y :=
    (A.chart k).left_inv hyk
  have hτa : AnalyticAt ℂ (A.chart k ∘ (A.chart j).symm) y := A.holo j k y ⟨hy, hyk⟩
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart k).open_source
  have hsm : ∀ i, ContDiffAt ℝ 2 ((Φ i).φ ((A.chart j).symm y) ∘ (A.chart k).symm)
      ((A.chart k ∘ (A.chart j).symm) y) := fun i =>
    potSmoothAt A (Φ i) (hΦ i) _ k ⟨(A.chart k).map_source hyk, by
      simp only [Set.mem_preimage, Function.comp_apply, hback]; exact (Φ i).mem_U _⟩
  have hcomp := ReciprocityTheory.AnForm.A.maDens_comp (fun i => (Φ i).φ ((A.chart j).symm y) ∘ (A.chart k).symm)
    (A.chart k ∘ (A.chart j).symm) y hτa hsm

  have hL : locDens A Φ j y = maDens (fun i => ((Φ i).φ ((A.chart j).symm y) ∘ (A.chart k).symm) ∘
      (A.chart k ∘ (A.chart j).symm)) y := by
    unfold locDens
    apply maDens_congr_hessC
    intro i
    refine hessCGerm _ _ _ ?_
    filter_upwards [hO.mem_nhds ⟨hy, hyk⟩] with y' hy'
    simp only [Function.comp_apply, (A.chart k).left_inv hy'.2]
  rw [hL, hcomp, ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq]
  unfold locDens
  simp only [Function.comp_apply, hback]
  rfl
end ReciprocityTheory.AnForm.M

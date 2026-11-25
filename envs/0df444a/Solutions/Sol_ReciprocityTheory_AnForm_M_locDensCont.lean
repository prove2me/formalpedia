-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.locDensCont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:45:56.686682+00:00
-- url     : https://prove2.me/submissions/d5abf5cb-6f3b-4754-b7c6-397438ef321f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Theorems.Thm_ReciprocityTheory_AnForm_M_potSmoothOn
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensBase
import Theorems.Thm_ReciprocityTheory_AnForm_M_maDens_continuousOn

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
theorem _root_.solution : LocDensContStatement := by
  intro e X _ A Φ hΦ j y0 hy0

  let x : Fin e → X := fun _ => (A.chart j).symm y0
  let V := (A.chart j).target ∩ (A.chart j).symm ⁻¹' ⋂ i, (Φ i).U (x i)
  have hV : IsOpen V :=
    (A.chart j).isOpen_inter_preimage_symm (isOpen_iInter_of_finite fun i => (Φ i).isOpen_U (x i))
  have hy0V : y0 ∈ V := ⟨hy0, Set.mem_iInter.2 fun i => (Φ i).mem_U _⟩
  have hsm : ∀ i, ContDiffOn ℝ 2 (fun y' => (Φ i).φ (x i) ((A.chart j).symm y')) V := fun i =>
    (potSmoothOn A (Φ i) (hΦ i) (x i) j).mono fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2 i⟩
  have hg := (maDens_continuousOn _ V hV hsm).continuousAt (hV.mem_nhds hy0V)
  have hev : (maDens fun i y' => (Φ i).φ (x i) ((A.chart j).symm y')) =ᶠ[nhds y0]
      locDens A Φ j := by
    filter_upwards [hV.mem_nhds hy0V] with y hy
    exact (locDensBase A Φ hΦ j y hy.1 x fun i => Set.mem_iInter.1 hy.2 i).symm
  exact (hg.congr hev).continuousWithinAt
end ReciprocityTheory.AnForm.M

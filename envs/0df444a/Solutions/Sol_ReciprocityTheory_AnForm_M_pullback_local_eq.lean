-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pullback_local_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:38.149464+00:00
-- url     : https://prove2.me/submissions/a3ea71af-e8c0-4044-a3bc-51a7823f0434

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback
import Theorems.Thm_ReciprocityTheory_AnForm_M_holoMap_preimage_mem_nhds

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
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e' X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h)
    (P : LocPot X) (j : Fin B.n) (k : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (B.chart j).target) (hk : h ((B.chart j).symm y) ∈ (A.chart k).source) :
    (fun y' => P.φ (h ((B.chart j).symm y)) (h ((B.chart j).symm y'))) =ᶠ[𝓝 y]
      (P.φ (h ((B.chart j).symm y)) ∘ (A.chart k).symm) ∘
        (A.chart k ∘ h ∘ (B.chart j).symm) := by
  filter_upwards [holoMap_preimage_mem_nhds hh j k hy hk] with y' hy'
  simp only [Function.comp_apply]
  rw [(A.chart k).left_inv hy'.2]
end ReciprocityTheory.AnForm.M

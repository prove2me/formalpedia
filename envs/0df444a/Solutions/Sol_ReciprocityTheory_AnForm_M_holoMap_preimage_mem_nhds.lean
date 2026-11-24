-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.holoMap_preimage_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:55.464829+00:00
-- url     : https://prove2.me/submissions/da766777-445f-4d81-8e5a-5fd8d69c7332

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback

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
theorem _root_.solution {e e' : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {A : FinHolAtlas e' X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (j : Fin B.n) (k : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (B.chart j).target) (hk : h ((B.chart j).symm y) ∈ (A.chart k).source) :
    (B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source) ∈ 𝓝 y := by
  have hs : IsOpen (h ⁻¹' (A.chart k).source) := (A.chart k).open_source.preimage hh.1
  exact ((B.chart j).isOpen_inter_preimage_symm hs).mem_nhds ⟨hy, hk⟩
end ReciprocityTheory.AnForm.M

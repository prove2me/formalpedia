-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.potential_contDiffAt_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:48.141602+00:00
-- url     : https://prove2.me/submissions/c05b7167-8b5d-4172-9d80-3655d90d906f

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
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} (hP : IsPotential A P) (x : X) (k : Fin A.n) {z : Fin e → ℂ}
    (hz : z ∈ (A.chart k).target) (hzU : (A.chart k).symm z ∈ P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) z := by
  have hS : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U x) :=
    (A.chart k).isOpen_inter_preimage_symm (P.isOpen_U x)
  refine ((hP.1 x k).contDiffAt (hS.mem_nhds ⟨hz, hzU⟩)).of_le ?_
  exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
end ReciprocityTheory.AnForm.M

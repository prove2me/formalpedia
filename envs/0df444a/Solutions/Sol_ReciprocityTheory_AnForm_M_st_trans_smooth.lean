-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_trans_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:34.834374+00:00
-- url     : https://prove2.me/submissions/b52afac6-7660-41ed-8229-bbac1e51c0ca

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) (j k : Fin A.n) :
    ContDiffOn ℝ ∞ (A.chart k ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) := by
  exact fun y hy => (((A.holo j k y hy).contDiffAt (n := ∞)).restrict_scalars ℝ).contDiffWithinAt
end ReciprocityTheory.AnForm.M

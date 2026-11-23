-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.contDiffAt_of_isPotential
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:23.884481+00:00
-- url     : https://prove2.me/submissions/67dd0327-c6f0-4312-8634-a77fe2cd2985

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential

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
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P)
    (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ContDiffAt ℝ ∞ (P.φ x ∘ (A.chart j).symm) y :=
  (hP.1 x j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds hy)
end ReciprocityTheory.AnForm.M

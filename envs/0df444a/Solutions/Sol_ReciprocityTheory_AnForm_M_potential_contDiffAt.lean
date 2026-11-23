-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.potential_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:47.886642+00:00
-- url     : https://prove2.me/submissions/a7b2b25a-6ac6-439f-a23b-e573b83093fd

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt

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
open scoped ContDiff ComplexOrder
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P)
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) :
    ContDiffAt ℝ 2 (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
  have h := hP.1 ((A.chart j).symm y) j
  have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U ((A.chart j).symm y) ∈ 𝓝 y :=
    ((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U _)).mem_nhds ⟨hy, P.mem_U _⟩
  exact (h.contDiffAt hmem).of_le (by norm_cast)
end ReciprocityTheory.AnForm.M

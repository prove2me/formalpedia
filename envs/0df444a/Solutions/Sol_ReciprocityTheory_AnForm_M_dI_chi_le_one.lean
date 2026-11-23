-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.dI_chi_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:34.1042+00:00
-- url     : https://prove2.me/submissions/bda67fa0-c1b1-4f7a-b879-5caf9b52ad3a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA

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
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) (P : ChartPartition A) (k : Fin A.n) (x : X) :
    P.χ k x ≤ 1 := by
  calc P.χ k x ≤ ∑ j, P.χ j x := Finset.single_le_sum (fun j _ => P.nonneg j x) (Finset.mem_univ k)
    _ = 1 := P.sum_eq_one x
end ReciprocityTheory.AnForm.M

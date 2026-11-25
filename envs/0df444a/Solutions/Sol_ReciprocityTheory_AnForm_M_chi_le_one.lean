-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.chi_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:12:56.848305+00:00
-- url     : https://prove2.me/submissions/93ccc04b-f537-4b37-8e91-ffa1e2b57e7f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Set Filter Topology
open scoped ContDiff ENNReal NNReal
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    (P : ChartPartition A) (j : Fin A.n) (x : X) : P.χ j x ≤ 1 := by
  exact (Finset.single_le_sum (f := fun i => P.χ i x) (fun i _ => P.nonneg i x)
    (Finset.mem_univ j)).trans (P.sum_eq_one x).le
end ReciprocityTheory.AnForm.M

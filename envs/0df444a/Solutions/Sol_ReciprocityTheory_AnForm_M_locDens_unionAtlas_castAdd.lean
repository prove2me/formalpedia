-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.locDens_unionAtlas_castAdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:46.213212+00:00
-- url     : https://prove2.me/submissions/0dcbcfd8-2165-4608-a6c9-9273f67f33f4

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AtlasIndep

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
theorem _root_.solution (A B : FinHolAtlas e X) (h : A.Compatible B)
    (Φ : Fin e → LocPot X) (j : Fin A.n) :
    locDens (unionAtlas A B h) Φ (Fin.castAdd B.n j) = locDens A Φ j := by
  funext y
  simp only [locDens, unionAtlas_chart_castAdd]
end ReciprocityTheory.AnForm.M

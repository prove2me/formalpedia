-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.locDens_unionAtlas_natAdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:46.751772+00:00
-- url     : https://prove2.me/submissions/48521dc1-aa9e-499f-9672-9dffa2a04a5d

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
    (Φ : Fin e → LocPot X) (k : Fin B.n) :
    locDens (unionAtlas A B h) Φ (Fin.natAdd A.n k) = locDens B Φ k := by
  funext y
  simp only [locDens, unionAtlas_chart_natAdd]
end ReciprocityTheory.AnForm.M

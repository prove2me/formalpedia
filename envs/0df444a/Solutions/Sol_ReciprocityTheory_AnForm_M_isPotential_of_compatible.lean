-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.isPotential_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:13:34.768469+00:00
-- url     : https://prove2.me/submissions/e37afe72-25e3-41ce-aef3-08bea7ad0a49

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AtlasIndep
import Theorems.Thm_ReciprocityTheory_AnForm_M_holoOn_of_compatible

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
theorem _root_.solution {A B : FinHolAtlas e X} (h : A.Compatible B) {P : LocPot X}
    (hP : IsPotential A P) : IsPotential B P := by
  refine ⟨fun x => smoothOn_of_compatible h (P.isOpen_U x) (hP.1 x), fun x x' y hy => ?_⟩
  obtain ⟨W, hW, hyW, G, hG, hφ⟩ := hP.2 x x' y hy
  exact ⟨W, hW, hyW, G, holoOn_of_compatible h hW hG, hφ⟩
end ReciprocityTheory.AnForm.M

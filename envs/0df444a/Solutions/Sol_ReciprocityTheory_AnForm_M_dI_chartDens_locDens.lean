-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.dI_chartDens_locDens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:07:26.747543+00:00
-- url     : https://prove2.me/submissions/6e6d80ff-bc97-4fcc-bee6-4eec3e130ec3

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensChart


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
theorem _root_.solution (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) : DIChartDens A (locDens A Φ) :=
  fun a b z hz hz2 => locDensChart A Φ hΦ a b z hz hz2
end ReciprocityTheory.AnForm.M

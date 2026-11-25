-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.mIntAtlasIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:44:23.362197+00:00
-- url     : https://prove2.me/submissions/5143e7b8-4a34-49ab-a067-391efa20752e

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AtlasIndep
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_of_compatible
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntegrable_of_compatible
import Theorems.Thm_ReciprocityTheory_AnForm_M_integralWith_extendLeft
import Theorems.Thm_ReciprocityTheory_AnForm_M_integralWith_extendRight
import Theorems.Thm_ReciprocityTheory_AnForm_M_existsPartition
import Theorems.Thm_ReciprocityTheory_AnForm_M_integralWithIndep
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntEq


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
theorem _root_.solution : MIntAtlasIndepStatement := by
  intro e X _ _ _ A B h Φ hΦ g hg
  have hgB : MIntegrable B Φ g := mIntegrable_of_compatible h Φ hΦ hg
  refine ⟨hgB, ?_⟩
  have hU : ∀ i, IsPotential (unionAtlas A B h) (Φ i) := fun i =>
    isPotential_of_compatible (compatible_unionAtlas_left A B h) (hΦ i)
  have hgU : MIntegrable (unionAtlas A B h) Φ g :=
    mIntegrable_of_compatible (compatible_unionAtlas_left A B h) Φ hΦ hg
  have hΦB : ∀ i, IsPotential B (Φ i) := fun i => isPotential_of_compatible h (hΦ i)
  obtain ⟨P⟩ := existsPartition A
  obtain ⟨Q⟩ := existsPartition B
  rw [mIntEq A P Φ hΦ g hg, mIntEq B Q Φ hΦB g hgB, ← integralWith_extendLeft h P Φ g,
    ← integralWith_extendRight h Q Φ g]
  exact integralWithIndep _ _ _ Φ hU g hgU
end ReciprocityTheory.AnForm.M

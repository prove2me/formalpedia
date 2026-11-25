-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.holoOn_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:27.985801+00:00
-- url     : https://prove2.me/submissions/df2d0d4b-4505-4540-a5be-2b62e6b37fb7

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
theorem _root_.solution {A B : FinHolAtlas e X} (h : A.Compatible B) {U : Set X}
    (hU : IsOpen U) {g : X → ℂ} (hg : A.HoloOn U g) : B.HoloOn U g := by
  intro j y hy
  obtain ⟨k, hT, hTt, hTs, hev⟩ := compat_local h j hy.1
  have hTs' : (A.chart k).symm ((A.chart k) ((B.chart j).symm y)) ∈ U := by
    rw [hTs]
    exact hy.2
  exact (AnalyticAt.comp (g := g ∘ (A.chart k).symm) (f := A.chart k ∘ (B.chart j).symm)
    (hg k _ ⟨hTt, hTs'⟩) hT).congr (hev g).symm
end ReciprocityTheory.AnForm.M

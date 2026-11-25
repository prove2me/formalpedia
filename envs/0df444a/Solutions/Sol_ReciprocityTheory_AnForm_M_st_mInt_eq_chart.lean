-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_mInt_eq_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:13:22.720412+00:00
-- url     : https://prove2.me/submissions/18c8010f-a720-4575-ac2b-fba464c7b0e4

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Theorems.Thm_ReciprocityTheory_AnForm_M_existsPartition
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntLocalize
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntegrableCont


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Ψ : Fin e → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (j : Fin A.n) (g : X → ℝ)
    (hg : Continuous g) (hgs : tsupport g ⊆ (A.chart j).source) :
    mInt A Ψ g = ∫ y in (A.chart j).target, g ((A.chart j).symm y) * locDens A Ψ j y := by
  unfold mInt
  rw [dif_pos (existsPartition A)]
  exact mIntLocalize A _ Ψ hΨ j g hgs (mIntegrableCont A Ψ hΨ g hg)
end ReciprocityTheory.AnForm.M

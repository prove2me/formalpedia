-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_mInt_congr_phi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:15.459001+00:00
-- url     : https://prove2.me/submissions/6cae3304-7a7d-408a-89f9-62bc611714ed

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA

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
theorem _root_.solution (A : FinHolAtlas e X) {Φ Ψ : Fin e → LocPot X}
    (h : ∀ i, (Φ i).φ = (Ψ i).φ) (g : X → ℝ) : mInt A Φ g = mInt A Ψ g := by
  have h1 : ∀ j y, locDens A Φ j y = locDens A Ψ j y := fun j y => by
    unfold locDens; simp only [h]
  unfold mInt integralWith
  simp only [h1]
end ReciprocityTheory.AnForm.M

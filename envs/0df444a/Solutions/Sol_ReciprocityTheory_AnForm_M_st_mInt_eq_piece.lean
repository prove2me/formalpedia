-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_mInt_eq_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:26:58.668291+00:00
-- url     : https://prove2.me/submissions/9d18bc59-a249-46a4-a262-83fa1f71dd72

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_mInt_eq_chart

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
    (Ψ : Fin e → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (j : Fin A.n) (G : Set X)
    (hG : G ⊆ (A.chart j).source) (g : X → ℝ) (hg : Continuous g) (hgs : tsupport g ⊆ G) :
    mInt A Ψ g = ∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' G,
      g ((A.chart j).symm y) * locDens A Ψ j y := by
  rw [st_mInt_eq_chart A Ψ hΨ j g hg (hgs.trans hG)]
  refine setIntegral_eq_of_subset_of_forall_diff_eq_zero (A.chart j).open_target.measurableSet
    inter_subset_left ?_
  intro y hy
  have hyG : (A.chart j).symm y ∉ G := fun h' => hy.2 ⟨hy.1, h'⟩
  have hg0 : g ((A.chart j).symm y) = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hyG (hgs h'))
  rw [hg0, zero_mul]
end ReciprocityTheory.AnForm.M

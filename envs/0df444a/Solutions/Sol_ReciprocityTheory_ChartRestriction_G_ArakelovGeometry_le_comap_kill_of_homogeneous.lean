-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.le_comap_kill_of_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:02:26.555912+00:00
-- url     : https://prove2.me/submissions/126b9c5d-ab7c-40d1-adf4-fc43dfa2962f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_TwoLeKrullDimOfRelevantPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_i2kill_homog_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_i2kill_homog_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {q : Ideal (MRing ι)} (hq : IsMultiHomogIdeal q) (k : K) :
    q ≤ q.comap (i2kill k) := by
  obtain ⟨S, hS, rfl⟩ := hq
  rw [Ideal.span_le]
  intro s hsS
  obtain ⟨a, ha⟩ := hS s hsS
  rw [SetLike.mem_coe, Ideal.mem_comap]
  by_cases h : a k = 0
  · rw [i2kill_homog_zero ha h]; exact Ideal.subset_span hsS
  · rw [i2kill_homog_pos ha h]; exact zero_mem _
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.eq_of_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:32:03.768875+00:00
-- url     : https://prove2.me/submissions/9aad8254-3ef2-4c9b-835e-2d610c3ec36a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_coeff_foldr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_sum_single_toList

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
theorem _root_.solution (F G : MvPowerSeries σ ℂ)
    (h : ∀ l : List σ, constantCoeff (l.foldr (fun q H => pderiv ℂ q H) F) =
      constantCoeff (l.foldr (fun q H => pderiv ℂ q H) G)) : F = G := by
  ext m
  obtain ⟨c, hc, hcF⟩ := coeff_foldr (Finsupp.toMultiset m).toList m
  have h1 := h (Finsupp.toMultiset m).toList
  obtain ⟨c0, hc0, h0⟩ := coeff_foldr (Finsupp.toMultiset m).toList 0
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    h0, h0, zero_add, sum_single_toList] at h1
  exact mul_left_cancel₀ hc0 h1
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf

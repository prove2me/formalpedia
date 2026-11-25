-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.RhGradStatement_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:20:11.198313+00:00
-- url     : https://prove2.me/submissions/4ef5dbfe-2ba5-40df-8e5c-dd5f2e194278

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgE_rhGrad_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.RgE
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution : RhGradStatement := by
  intro f p q v hv ξ
  by_cases h : 0 < f ∧ 0 < min p q
  · exact rhGrad_main h.1 h.2 v hv ξ
  · have hn : nD f p q = 0 := by
      simp only [nD]
      rcases Nat.eq_zero_or_pos f with hf | hf
      · simp [hf]
      · have hm : ¬ 0 < min p q := fun hm => h ⟨hf, hm⟩
        rcases Nat.min_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hm) with hp | hq
        · simp [hp]
        · simp [hq]
    haveI : IsEmpty (Fin (nD f p q)) := by rw [hn]; infer_instance
    simp [leviV]
end ReciprocityTheory.ChartRestriction.G.AR.Up

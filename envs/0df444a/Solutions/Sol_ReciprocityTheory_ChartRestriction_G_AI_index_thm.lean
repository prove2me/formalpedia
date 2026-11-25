-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.index_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:25.594038+00:00
-- url     : https://prove2.me/submissions/97041491-7a37-48c5-9664-de64b4c09728

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_IndexSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_CardQuotEqNatAbsNorm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_card_quot_eq_natAbs_norm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_norm_int_eq_norm_rat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_abs_norm_eq_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution : IndexStatement := by
  intro K _ _ O hfree hfin hrank f hf
  haveI := hfree
  haveI := hfin
  have hc := card_quot_eq_natAbs_norm f hf
  have hn := norm_int_eq_norm_rat O hrank f
  have hprod := abs_norm_eq_prod (f : K)
  have h1 : (Nat.card (O ⧸ Ideal.span {f}) : ℝ) = |(Algebra.norm ℚ (f : K) : ℝ)| := by
    rw [hc, ← hn]
    simp [Nat.cast_natAbs, Int.cast_abs, Rat.cast_intCast]
  refine ⟨h1, ?_⟩
  rw [h1, hprod, Real.log_prod (fun σ _ => ?_)]
  exact norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr (fun h0 => hf (Subtype.ext h0)))
end ReciprocityTheory.ChartRestriction.G.AI

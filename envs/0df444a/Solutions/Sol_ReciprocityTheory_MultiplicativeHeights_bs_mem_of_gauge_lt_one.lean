-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.bs_mem_of_gauge_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:31:10.92312+00:00
-- url     : https://prove2.me/submissions/45ddcc65-21f8-4857-8274-e770751286ed

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_BalancedSchwarz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Metric Set
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {s : Set E}
    (hs : IsOpen s) (hb : Balanced ℂ s) (h0 : (0 : E) ∈ s) {x : E} (hx : gauge s x < 1) :
    x ∈ s := by
  have habs : Absorbent ℝ s := absorbent_nhds_zero (hs.mem_nhds h0)
  obtain ⟨b, hb0, hb1, y, hy, rfl⟩ := exists_lt_of_gauge_lt habs hx
  have : (b : ℂ) • y ∈ s := hb.smul_mem (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]; exact hb1.le) hy
  simpa [Complex.coe_smul] using this
end ReciprocityTheory.MultiplicativeHeights

-- Prove2me | solution 1 for PI.Residue.sum_range_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:13:36.967621+00:00
-- url     : https://prove2.me/submissions/92af8dd9-3531-493d-bff1-2e663c57a95f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_SumRangeLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open MeasureTheory intervalIntegral
namespace PI.Residue
theorem _root_.solution (s : ℝ) (hs : 1 < s) (N : ℕ) :
    ∑ i ∈ Finset.range N, ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-s) ≤ 1 / (s - 1) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc (1 : ℝ) (1 + N)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have h1 := hanti.sum_le_integral
  refine h1.trans ?_
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + N) := by
    rw [Set.uIcc_of_le (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by linarith, h0⟩)]
  have hpos : 0 < s - 1 := by linarith
  have hN : 0 ≤ ((1 : ℝ) + N) ^ (-s + 1) := by positivity
  rw [Real.one_rpow, show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div, neg_sub]
  rw [show -(s - 1) = -s + 1 by ring]
  apply div_le_div_of_nonneg_right _ hpos.le
  linarith
end PI.Residue

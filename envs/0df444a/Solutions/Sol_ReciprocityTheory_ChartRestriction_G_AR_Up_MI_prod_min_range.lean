-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.prod_min_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:49.310342+00:00
-- url     : https://prove2.me/submissions/8837f0e2-1599-4aa6-bbb0-8a7558481588

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfI
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData Finset
noncomputable section
attribute [local instance] Classical.propDecidable
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (f : ℕ → ℝ) (n : ℕ) :
    ∏ a ∈ range n, ∏ b ∈ range n, f (min a b) = (∏ i ∈ range n, (∏ k ∈ range i, f k) ^ 2) * ∏ k ∈ range n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∀ a ∈ range n, ∏ b ∈ range (n + 1), f (min a b) = (∏ b ∈ range n, f (min a b)) * f a := by
      intro a ha
      rw [prod_range_succ, min_eq_left (le_of_lt (mem_range.mp ha))]
    have h2 : ∏ b ∈ range (n + 1), f (min n b) = (∏ b ∈ range n, f b) * f n := by
      rw [prod_range_succ, min_self]
      congr 1
      exact prod_congr rfl fun b hb => by rw [min_eq_right (le_of_lt (mem_range.mp hb))]
    rw [prod_range_succ (fun a => ∏ b ∈ range (n + 1), f (min a b)) n, prod_congr rfl h1, prod_mul_distrib, ih, h2,
      prod_range_succ (fun i => (∏ k ∈ range i, f k) ^ 2) n, prod_range_succ f n]
    ring
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI

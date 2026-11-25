-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.IW.sbp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:39:16.901496+00:00
-- url     : https://prove2.me/submissions/ed624b2e-fbb3-4cab-8b52-f539e43cfda2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.IW
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff Matrix ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW
theorem _root_.solution (L : ℕ → ℝ) : ∀ r : ℕ, ∑ i ∈ Finset.range r, ((2 * i : ℝ) - ((r : ℝ) - 1)) * (L (i + 1) - L i) =
    ((r : ℝ) - 1) * L r - 2 * ∑ i ∈ Finset.range r, L i + ((r : ℝ) + 1) * L 0
  | 0 => by simp
  | r + 1 => by
    have ih := solution L r
    have htel : ∑ i ∈ Finset.range r, (L (i + 1) - L i) = L r - L 0 := Finset.sum_range_sub L r
    have hsplit : ∑ i ∈ Finset.range r, ((2 * i : ℝ) - (((r + 1 : ℕ) : ℝ) - 1)) * (L (i + 1) - L i) =
        ∑ i ∈ Finset.range r, ((2 * i : ℝ) - ((r : ℝ) - 1)) * (L (i + 1) - L i) -
          ∑ i ∈ Finset.range r, (L (i + 1) - L i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [Finset.sum_range_succ, hsplit, ih, htel, Finset.sum_range_succ]
    push_cast
    ring
end ReciprocityTheory.ChartRestriction.G.AR.Up.IW

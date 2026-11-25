-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FM.Jp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:39:36.832454+00:00
-- url     : https://prove2.me/submissions/bbf40684-cc38-4709-9496-f3ac33595b53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FM
open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open scoped ENNReal NNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
attribute [local instance] haarF haarIx
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM
theorem _root_.solution {C : Set (Frame X.Ψ r)} {q : Frame X.Ψ r}
    (h : ∀ y : UpI X.Ψ r → ℂ, (∀ τ b, y (dI τ b) ≠ 0) → rmul q (UF X y) ∉ C) : Jp X C q = 0 := by
  unfold Jp
  have hz : ∀ y : UpI X.Ψ r → ℂ, (if ∀ τ b, y (dI τ b) ≠ 0 then
      ENNReal.ofReal (Complex.normSq (jacU y)) * C.indicator 1 (rmul q (UF X y)) else 0) = 0 := by
    intro y
    split_ifs with hy
    · simp [Set.indicator, h y hy]
    · rfl
  simp_rw [hz]
  exact lintegral_zero
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM

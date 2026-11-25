-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lintegral__C_84e056a32217
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:18.940932+00:00
-- url     : https://prove2.me/submissions/30c67a22-0a08-466b-a849-5215e47b32ac

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (F : (LoI X.Ψ r → ℂ) → ENNReal) :
    ∫⁻ z, F (ΦC X z) = Measure.addHaarScalarFactor (volume.map (ΦC X)) volume * ∫⁻ x, F x := by
  have h1 : (∫⁻ z, F (ΦC X z)) = ∫⁻ x, F x ∂(volume.map (ΦC X)) :=
    (lintegral_map_equiv F (ΦC X).toHomeomorph.toMeasurableEquiv).symm
  calc (∫⁻ z, F (ΦC X z)) = ∫⁻ x, F x ∂(volume.map (ΦC X)) := h1
    _ = ∫⁻ x, F x ∂(Measure.addHaarScalarFactor (volume.map (ΦC X)) volume • volume) := by
        rw [← Measure.isAddLeftInvariant_eq_smul]
    _ = _ := lintegral_smul_measure _ _
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI

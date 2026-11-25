-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FM.lintegral_ufC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:40:58.625997+00:00
-- url     : https://prove2.me/submissions/9cc68293-d611-4eba-af57-d2c82dddba87

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
theorem _root_.solution (F : Frame X.Ψ r → ℝ≥0∞) :
    ∫⁻ v, F (ufC X v) = Measure.addHaarScalarFactor (volume.map (ufC X)) volume * ∫⁻ x, F x := by
  haveI : (volume.map (ufC X)).IsAddHaarMeasure := (ufC X).isAddHaarMeasure_map volume
  have e1 : ∫⁻ v, F (ufC X v) = ∫⁻ x, F x ∂(volume.map (ufC X)) :=
    (lintegral_map_equiv F (ufC X).toHomeomorph.toMeasurableEquiv).symm
  rw [e1]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (volume.map (ufC X)) volume]
  rw [lintegral_smul_measure]
  rfl
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
